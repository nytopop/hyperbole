use super::{
    reply::Reply,
    tree::{Parsed, Parser, Segment},
    Response,
};
use frunk_core::{
    coproduct::{CNil, CoprodUninjector, Coproduct},
    hlist::{HCons, HNil, Plucker, Sculptor},
};
use futures::future::{ready, FutureExt, Ready, TryFutureExt};
use std::{future::Future, marker::PhantomData, ops::Add, sync::Arc};

#[cfg(doc)]
use futures::future::BoxFuture;

pub trait Coprod {}

impl Coprod for CNil {}
impl<H, T> Coprod for Coproduct<H, T> {}

pub trait CoprodAppend<T> {
    type Output;

    fn appendl(self) -> Self::Output;

    fn appendr(right: T) -> Self::Output;
}

impl<T> CoprodAppend<T> for CNil {
    type Output = T;

    #[inline]
    fn appendl(self) -> Self::Output {
        match self {}
    }

    #[inline]
    fn appendr(right: T) -> Self::Output {
        right
    }
}

impl<T, Head, Tail: CoprodAppend<T>> CoprodAppend<T> for Coproduct<Head, Tail> {
    type Output = Coproduct<Head, <Tail as CoprodAppend<T>>::Output>;

    #[inline]
    fn appendl(self) -> Self::Output {
        match self {
            Coproduct::Inl(l) => Coproduct::Inl(l),
            Coproduct::Inr(r) => Coproduct::Inr(Tail::appendl(r)),
        }
    }

    #[inline]
    fn appendr(right: T) -> Self::Output {
        Coproduct::Inr(Tail::appendr(right))
    }
}

macro_rules! derive_clone_new_3 {
    ($t:ty where $( $p:ident $( : $bound:ident )? ),+) => {
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

    type Future = Ready<Result<(Self::Output, Self::Params), Self::Error>>;

    #[inline]
    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        ready(Ok((req, p)))
    }
}

#[derive(Clone)]
pub struct Inject<L, T> {
    prev: L,
    value: T,
}

impl<L, T> Inject<L, T> {
    pub fn new(prev: L, value: T) -> Self {
        Self { prev, value }
    }
}

impl<Req, P, L, T> Link<Req, P> for Inject<L, T>
where
    L: Link<Req, P>,
    T: Clone + Send,
{
    type Output = HCons<T, <L as Link<Req, P>>::Output>;

    type Params = <L as Link<Req, P>>::Params;

    type Error = <L as Link<Req, P>>::Error;

    type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let head = self.value.clone();

        self.prev
            .handle_link(req, p)
            .map_ok(move |(tail, p)| (HCons { head, tail }, p))
    }
}

#[derive(Clone)]
pub struct InjectAll<L, T> {
    prev: L,
    value: T,
}

impl<L, T> InjectAll<L, T> {
    pub fn new(prev: L, value: T) -> Self {
        Self { prev, value }
    }
}

impl<Req, P, L, T> Link<Req, P> for InjectAll<L, T>
where
    L: Link<Req, P>,
    <L as Link<Req, P>>::Output: Add<T>,
    Add2<<L as Link<Req, P>>::Output, T>: Send,
    T: Clone + Send,
{
    type Output = Add2<<L as Link<Req, P>>::Output, T>;

    type Params = <L as Link<Req, P>>::Params;

    type Error = <L as Link<Req, P>>::Error;

    type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let rest = self.value.clone();

        self.prev
            .handle_link(req, p)
            .map_ok(move |(head, p)| (head + rest, p))
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

    type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        self.prev.handle_link(req, p).map_ok(move |(stack, p)| {
            let (take, rest) = stack.sculpt();
            let merge = next(take);
            (rest + merge, p)
        })
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

    type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        self.prev.handle_link(req, p).map(move |res| {
            let (stack, p) = res.map_err(Coproduct::Inr)?;
            let (take, rest) = stack.sculpt();
            let merge = next(take).map_err(Coproduct::Inl)?;
            Ok((rest + merge, p))
        })
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

    type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        (self.prev.handle_link(req, p)).and_then(|(stack, p)| async move {
            let (take, rest) = stack.sculpt();
            let merge = next(take).await;
            Ok((rest + merge, p))
        })
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

    type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        self.prev.handle_link(req, p).then(|res| async move {
            let (stack, p) = res.map_err(Coproduct::Inr)?;
            let (take, rest) = stack.sculpt();
            let merge = next(take).await.map_err(Coproduct::Inl)?;
            Ok((rest + merge, p))
        })
    }
}

pub struct MapErrs<L, F> {
    prev: L,
    next: Arc<F>,
    tag: PhantomData<()>,
}

derive_clone_new_3! { MapErrs<L, F> where L: Clone, F }

impl<Req, P, L, F, E> Link<Req, P> for MapErrs<L, F>
where
    L: Link<Req, P>,
    F: Fn(<L as Link<Req, P>>::Error) -> E + Sync + Send,
    E: Coprod + Reply,
{
    type Output = <L as Link<Req, P>>::Output;

    type Params = <L as Link<Req, P>>::Params;

    type Error = E;

    type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        self.prev.handle_link(req, p).map_err(move |e| next(e))
    }
}

pub struct MapErr<L, F, E, Ix> {
    prev: L,
    next: Arc<F>,
    tag: PhantomData<fn(E, Ix)>,
}

derive_clone_new_3! { MapErr<L, F, E, Ix> where L: Clone, F, E, Ix }

impl<Req, P, L, F, E, Ix, R> Link<Req, P> for MapErr<L, F, E, Ix>
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

    type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = self.next.clone();

        (self.prev.handle_link(req, p)).map_err(move |e| match e.uninject() {
            Ok(err) => Coproduct::Inl(next(err)),
            Err(no) => Coproduct::Inr(no),
        })
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

    <L as Link<Req, P>>::Output: Add<Sub>,
    Add2<<L as Link<Req, P>>::Output, Sub>: Send,

    <L as Link<Req, P>>::Params: Plucker<Parsed<Sub>, Ix>,
    <<L as Link<Req, P>>::Params as Plucker<Parsed<Sub>, Ix>>::Remainder: Send,

    <L as Link<Req, P>>::Error: CoprodAppend<<Sub as Parser<Segment>>::Error>,
    <<L as Link<Req, P>>::Error as CoprodAppend<<Sub as Parser<Segment>>::Error>>::Output: Reply,

    Sub: Parser<Segment>,
{
    type Output = Add2<<L as Link<Req, P>>::Output, Sub>;

    type Params = <<L as Link<Req, P>>::Params as Plucker<Parsed<Sub>, Ix>>::Remainder;

    type Error =
        <<L as Link<Req, P>>::Error as CoprodAppend<<Sub as Parser<Segment>>::Error>>::Output;

    type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        self.link.handle_link(req, p).map(|res| match res {
            Ok((stack, p)) => match p.pluck() {
                (Ok(ps), rem) => Ok((stack + ps, rem)),
                (Err(e), _) => Err(<<L as Link<Req, P>>::Error as CoprodAppend<
                    <Sub as Parser<Segment>>::Error,
                >>::appendr(e)),
            },
            Err(e) => Err(e.appendl()),
        })
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

    type Future = impl Future<Output = Result<(Self::Output, Self::Params), Self::Error>>;

    fn handle_link(&self, req: Req, p: P) -> Self::Future {
        let next = Arc::clone(&self.next);

        self.prev.handle_link(req, p).and_then(|(s, _)| async move {
            let (take, _) = s.sculpt();
            let reply = next(take).await;
            Ok((reply.into_response(), HNil))
        })
    }
}
