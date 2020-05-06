use super::{reply::Reply, Response};
use frunk_core::{
    coproduct::{CNil, CoprodUninjector, Coproduct},
    hlist::{HNil, Sculptor},
};
use futures::future::{FutureExt, TryFutureExt};
use std::{future::Future, marker::PhantomData, ops::Add, sync::Arc};

#[cfg(doc)]
use futures::future::BoxFuture;

/// A hack to make `type_alias_impl_trait` work with rustdoc.
///
/// When compiling under rustdoc, the left variant is used, while rustc will use the right
/// variant.
///
/// Tracking issue for the bug: https://github.com/rust-lang/rust/issues/65863
macro_rules! doc_hack {
    ($doc:expr, $not_doc:expr) => {
        #[cfg(doc)]
        {
            $doc
        }
        #[cfg(not(doc))]
        {
            $not_doc
        }
    };

    ($doc:item $not_doc:item) => {
        #[cfg(doc)]
        $doc
        #[cfg(not(doc))]
        $not_doc
    };
}

macro_rules! derive_clone_new_3 {
    ( $t:ty where $( $p:ident $( : $bound:ident )? ),+) => {
        impl<$( $p $( : $bound )? ),+> Clone for $t {
            fn clone(&self) -> Self {
                let prev = self.prev.clone();
                let next = self.next.clone();
                let tag = PhantomData;
                Self { prev, next, tag }
            }
        }

        impl<$( $p ),+> $t {
            pub fn new(prev: L, next: F) -> Self {
                let next = Arc::new(next);
                let tag = PhantomData;
                Self { prev, next, tag }
            }
        }
    };
}

pub type Add2<A, B> = <A as Add<B>>::Output;

pub trait Link<Req, P> {
    type Output: Send;

    type Params: Send;

    type Error: Reply;

    type Future: Future<Output = Result<(Self::Output, Self::Params), Self::Error>> + Send;

    fn handle_link(&self, req: Req, params: P) -> Self::Future;
}

#[derive(Copy, Clone)]
pub struct Base;

impl<Req: Send, P: Send> Link<Req, P> for Base {
    type Output = Req;

    type Params = P;

    type Error = CNil;

    doc_hack! {
        type Future = BoxFuture<'static, Result<(Self::Output, Self::Params), Self::Error>>;
        type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;
    }

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let fut = async { Ok((req, p)) };

        doc_hack! { Box::pin(fut), fut }
    }
}

pub struct Map<L, F, Args, Ix> {
    prev: L,
    next: Arc<F>,
    tag: PhantomData<fn(Args, Ix)>,
}

derive_clone_new_3! { Map<L, F, Args, Ix> where L: Clone, F, Args, Ix }

impl<Req, P, L, F, Args, Ix, Res> Link<Req, P> for Map<L, F, Args, Ix>
where
    L: Link<Req, P>,
    <L as Link<Req, P>>::Output: Sculptor<Args, Ix>,
    <<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder: Add<Res> + Send,
    <<<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder as Add<Res>>::Output: Send,

    F: Fn(Args) -> Res + Sync + Send,
{
    type Output =
        <<<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder as Add<Res>>::Output;

    type Params = <L as Link<Req, P>>::Params;

    type Error = <L as Link<Req, P>>::Error;

    doc_hack! {
        type Future = BoxFuture<'static, Result<(Self::Output, Self::Params), Self::Error>>;
        type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;
    }

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        let fut = self.prev.handle_link(req, p).map_ok(move |(stack, p)| {
            let (take, rest) = stack.sculpt();
            let merge = next(take);
            (rest + merge, p)
        });

        doc_hack! { Box::pin(fut) , fut }
    }
}

pub struct TryMap<L, F, Args, Ix> {
    prev: L,
    next: Arc<F>,
    tag: PhantomData<fn(Args, Ix)>,
}

derive_clone_new_3! { TryMap<L, F, Args, Ix> where L: Clone, F, Args, Ix }

impl<Req, P, L, F, Args, Ix, Res, E> Link<Req, P> for TryMap<L, F, Args, Ix>
where
    L: Link<Req, P>,
    <L as Link<Req, P>>::Output: Sculptor<Args, Ix>,
    <<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder: Add<Res> + Send,
    <<<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder as Add<Res>>::Output: Send,

    F: Fn(Args) -> Result<Res, E> + Sync + Send,
    E: Reply,
{
    type Output =
        <<<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder as Add<Res>>::Output;

    type Params = <L as Link<Req, P>>::Params;

    type Error = Coproduct<E, <L as Link<Req, P>>::Error>;

    doc_hack! {
        type Future = BoxFuture<'static, Result<(Self::Output, Self::Params), Self::Error>>;
        type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;
    }

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        let fut = self.prev.handle_link(req, p).map(move |res| {
            let (stack, p) = res.map_err(Coproduct::Inr)?;
            let (take, rest) = stack.sculpt();
            let merge = next(take).map_err(Coproduct::Inl)?;
            Ok((rest + merge, p))
        });

        doc_hack! { Box::pin(fut) , fut }
    }
}

pub struct Then<L, F, Args, Ix> {
    prev: L,
    next: Arc<F>,
    tag: PhantomData<fn(Args, Ix)>,
}

derive_clone_new_3! { Then<L, F, Args, Ix> where L: Clone, F, Args, Ix }

impl<Req, P, L, F, Args, Ix, Fut, Res> Link<Req, P> for Then<L, F, Args, Ix>
where
    L: Link<Req, P>,
    <L as Link<Req, P>>::Output: Sculptor<Args, Ix>,
    <<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder: Add<Res> + Send,
    <<<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder as Add<Res>>::Output: Send,

    F: Fn(Args) -> Fut + Sync + Send,
    Args: Send,
    Fut: Future<Output = Res> + Send,
{
    type Output =
        <<<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder as Add<Res>>::Output;

    type Params = <L as Link<Req, P>>::Params;

    type Error = <L as Link<Req, P>>::Error;

    doc_hack! {
        type Future = BoxFuture<'static, Result<(Self::Output, Self::Params), Self::Error>>;
        type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;
    }

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        let fut = (self.prev.handle_link(req, p)).and_then(|(stack, p)| async move {
            let (take, rest) = stack.sculpt();
            let merge = next(take).await;
            Ok((rest + merge, p))
        });

        doc_hack! { Box::pin(fut) , fut }
    }
}

pub struct TryThen<L, F, Args, Ix> {
    prev: L,
    next: Arc<F>,
    tag: PhantomData<fn(Args, Ix)>,
}

derive_clone_new_3! { TryThen<L, F, Args, Ix> where L: Clone, F, Args, Ix }

impl<Req, P, L, F, Args, Ix, Fut, Res, E> Link<Req, P> for TryThen<L, F, Args, Ix>
where
    L: Link<Req, P>,
    <L as Link<Req, P>>::Output: Sculptor<Args, Ix>,
    <<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder: Add<Res> + Send,
    <<<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder as Add<Res>>::Output: Send,

    Args: Send,
    F: Fn(Args) -> Fut + Sync + Send,
    Fut: Future<Output = Result<Res, E>> + Send,
    E: Reply + Send,
{
    type Output =
        <<<L as Link<Req, P>>::Output as Sculptor<Args, Ix>>::Remainder as Add<Res>>::Output;

    type Params = <L as Link<Req, P>>::Params;

    type Error = Coproduct<E, <L as Link<Req, P>>::Error>;

    doc_hack! {
        type Future = BoxFuture<'static, Result<(Self::Output, Self::Params), Self::Error>>;
        type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;
    }

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        let fut = self.prev.handle_link(req, p).then(|res| async move {
            let (stack, p) = res.map_err(Coproduct::Inr)?;
            let (take, rest) = stack.sculpt();
            let merge = next(take).await.map_err(Coproduct::Inl)?;
            Ok((rest + merge, p))
        });

        doc_hack! { Box::pin(fut) , fut }
    }
}

pub struct MapErr<L, F> {
    prev: L,
    next: Arc<F>,
    tag: PhantomData<()>,
}

derive_clone_new_3! { MapErr<L, F> where L: Clone, F }

impl<Req, P, L, F, E> Link<Req, P> for MapErr<L, F>
where
    L: Link<Req, P>,
    F: Fn(<L as Link<Req, P>>::Error) -> E + Sync + Send,
    E: Reply,
{
    type Output = <L as Link<Req, P>>::Output;

    type Params = <L as Link<Req, P>>::Params;

    type Error = E;

    doc_hack! {
        type Future = BoxFuture<'static, Result<(Self::Output, Self::Params), Self::Error>>;
        type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;
    }

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        let fut = self.prev.handle_link(req, p).map_err(move |e| next(e));

        doc_hack! { Box::pin(fut) , fut }
    }
}

pub struct CatchErr<L, F, E, Ix> {
    prev: L,
    next: Arc<F>,
    tag: PhantomData<fn(E, Ix)>,
}

derive_clone_new_3! { CatchErr<L, F, E, Ix> where L: Clone, F, E, Ix }

impl<Req, P, L, F, E, Ix, R> Link<Req, P> for CatchErr<L, F, E, Ix>
where
    L: Link<Req, P>,
    <L as Link<Req, P>>::Error: CoprodUninjector<E, Ix>,
    <<L as Link<Req, P>>::Error as CoprodUninjector<E, Ix>>::Remainder: Reply,

    F: Fn(E) -> R + Sync + Send,
    R: Reply,
{
    type Output = <L as Link<Req, P>>::Output;

    type Params = <L as Link<Req, P>>::Params;

    type Error = Coproduct<R, <<L as Link<Req, P>>::Error as CoprodUninjector<E, Ix>>::Remainder>;

    doc_hack! {
        type Future = BoxFuture<'static, Result<(Self::Output, Self::Params), Self::Error>>;
        type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;
    }

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        let fut = (self.prev.handle_link(req, p)).map_err(move |e| match e.uninject() {
            Ok(err) => Coproduct::Inl(next(err)),
            Err(no) => Coproduct::Inr(no),
        });

        doc_hack! { Box::pin(fut) , fut }
    }
}

pub struct Path<L, Sub, Ix> {
    link: L,
    tag: PhantomData<fn(Sub, Ix)>,
}

impl<L: Clone, Sub, Ix> Clone for Path<L, Sub, Ix> {
    fn clone(&self) -> Self {
        let link = self.link.clone();
        let tag = self.tag;
        Self { link, tag }
    }
}

impl<L, Sub, Ix> Path<L, Sub, Ix> {
    pub fn new(link: L) -> Self {
        let tag = PhantomData;
        Self { link, tag }
    }
}

impl<Req, P, L, Sub, Ix> Link<Req, P> for Path<L, Sub, Ix>
where
    L: Link<Req, P>,
    <L as Link<Req, P>>::Params: Sculptor<Sub, Ix>,
    <<L as Link<Req, P>>::Params as Sculptor<Sub, Ix>>::Remainder: Send,
    <L as Link<Req, P>>::Output: Add<Sub>,
    Add2<<L as Link<Req, P>>::Output, Sub>: Send,
{
    type Output = Add2<<L as Link<Req, P>>::Output, Sub>;

    type Params = <<L as Link<Req, P>>::Params as Sculptor<Sub, Ix>>::Remainder;

    type Error = <L as Link<Req, P>>::Error;

    doc_hack! {
        type Future = BoxFuture<'static, Result<(Self::Output, Self::Params), Self::Error>>;
        type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;
    }

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let fut = self.link.handle_link(req, p).map_ok(|(stack, p)| {
            let (ps, rem) = p.sculpt();
            (stack + ps, rem)
        });

        doc_hack! { Box::pin(fut) , fut }
    }
}

pub struct End<L, F, Args, Ix> {
    prev: L,
    next: Arc<F>,
    tag: PhantomData<fn(Args, Ix)>,
}

derive_clone_new_3! { End<L, F, Args, Ix> where L: Clone, F, Args, Ix }

impl<Req, P, L, F, Args, Ix, Fut, Resp> Link<Req, P> for End<L, F, Args, Ix>
where
    L: Link<Req, P>,
    <L as Link<Req, P>>::Output: Sculptor<Args, Ix>,

    Args: Send,
    F: Fn(Args) -> Fut + Sync + Send,
    Fut: Send + Future<Output = Resp>,
    Resp: Reply,
{
    type Output = Response;

    type Params = HNil;

    type Error = <L as Link<Req, P>>::Error;

    doc_hack! {
        type Future = BoxFuture<'static, Result<(Self::Output, Self::Params), Self::Error>>;
        type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;
    }

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = Arc::clone(&self.next);

        let fut = self.prev.handle_link(req, p).and_then(|(s, _)| async move {
            let (take, _) = s.sculpt();
            let reply = next(take).await;
            Ok((reply.into_response(), HNil))
        });

        doc_hack! { Box::pin(fut) , fut }
    }
}
