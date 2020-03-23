#![allow(unused_imports, dead_code, unused_variables)]

#[doc(inline)]
pub use frunk::{hlist, Hlist};

use frunk::{
    hlist::{HCons, HList, Sculptor},
    traits::ToRef,
};
use futures::future::{ready, FutureExt, LocalBoxFuture, Ready, TryFutureExt};
use hyper::{service::Service, Body};
use std::{
    convert::Infallible,
    future::Future,
    marker::PhantomData,
    ops::Add,
    task::{Context, Poll},
};

pub type Request = hyper::Request<Body>;

// TODO: can we do something like Router::from_generic?
// where there's a #[derive(Generic)] on some struct
#[derive(Copy, Clone, Debug)]
pub struct Router<I> {
    stack: I,
}

impl<I: HList> Router<I> {
    // TODO: methods
    // * get, post, put, delete, head, options, connect, patch, trace
    //
    // * ??? map, map_ref, and_then, and_ref (or just use subtree?)
    //
    // * subtree
    //
    // * subtree_path
    //
    // * into_service (or just impl MakeService???)
    pub fn new(stack: I) -> Self {
        Self { stack }
    }

    pub fn subtree(self) -> SubTree<I, Base> {
        SubTree {
            router: self,
            svc: Base,
        }
    }
}

// TODO: we could add a phantom type variable to know the state of the stack?
pub struct SubTree<I, S> {
    router: Router<I>,
    svc: S,
}

impl<'a, I: ToRef<'a>, S> SubTree<I, S> {
    // TODO: methods
    //
    // * map: moves a subset of the stack, merging its returned list in.
    // * map_ref: borrows a subset of the stack, merging its returned list in.
    // * map_mut: mutably borrows a subset of the stack, merging its returned list in.
    //
    // * and: fallible variant of map
    // * and_ref: fallible variant of map_ref
    // * and_mut: fallible variant of map_mut
    //
    // * with: move a subset of the stack, with a Service impl
    // * with_ref: borrow a subset of the stack, with a Service impl
    // * with_mut: mutable borrow a subset of the stack, with a Service impl
    //
    // all of the above are able to push new types onto the stack.
    //
    // * get, post, put, delete, head, options, connect, patch, trace:
    //  these all _move_ memory into themselves, because nothing can be after them.
    //
    // * path || subtree_path ?
    fn wrap_service<G, F: FnOnce(S) -> G>(self, wrap: F) -> SubTree<I, G> {
        let router = self.router;
        let svc = wrap(self.svc);

        SubTree { router, svc }
    }

    pub fn map<F, Fut, Ix, In, Im>(self, fun: F) -> SubTree<I, Map<S, F, Fut, Ix, In, Im>>
    where
        S: Service<(<I as ToRef<'a>>::Output, Request)>,

        F: Fn(In) -> Fut,

        Fut: Future<Output = Im>,

        <S as Service<(<I as ToRef<'a>>::Output, Request)>>::Response: Sculptor<In, Ix>,
    {
        self.wrap_service(|svc| Map {
            svc,
            fun,
            tag: PhantomData,
        })
    }

    pub fn map_ref<'b, F, Fut, Ix, In, Im>(
        self,
        fun: F,
    ) -> SubTree<I, MapRef<S, F, Fut, Ix, In, Im>>
    where
        S: Service<(<I as ToRef<'a>>::Output, Request)>,

        F: Fn(In) -> Fut,

        Fut: Future<Output = Im>,

        <S as Service<(<I as ToRef<'a>>::Output, Request)>>::Response: Add<Im> + ToRef<'b>,

        <<S as Service<(<I as ToRef<'a>>::Output, Request)>>::Response as ToRef<'b>>::Output:
            Sculptor<In, Ix>,
    {
        self.wrap_service(|svc| MapRef {
            svc,
            fun,
            tag: PhantomData,
        })
    }

    pub fn map_mut() {}

    pub fn and() {}
    pub fn and_ref() {}
    pub fn and_mut() {}

    pub fn with() {}
    pub fn with_ref() {}
    pub fn with_mut() {}

    pub fn get() {}
    pub fn post() {}
    pub fn put() {}
    pub fn delete() {}
    pub fn head() {}
    pub fn options() {}
    pub fn connect() {}
    pub fn patch() {}
    pub fn trace() {}

    pub fn path() {}

    /// Collapse the request processing stack, merging accumulated paths and handlers into the
    /// route tree.
    ///
    /// All type information is lost after this point!
    pub fn collapse(self) -> Router<I> {
        // TODO: do the collapsing
        self.router
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Base;

impl<I: HList> Service<(I, Request)> for Base {
    type Response = HCons<Request, I>;

    type Error = Infallible;

    type Future = Ready<Result<Self::Response, Self::Error>>;

    #[inline]
    fn poll_ready(&mut self, _: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    #[inline]
    fn call(&mut self, (inject, req): (I, Request)) -> Self::Future {
        ready(Ok(inject.prepend(req)))
    }
}

#[derive(Copy, Debug)]
pub struct Map<S, F, Fut, Ix, In, Im> {
    svc: S,
    fun: F,
    tag: PhantomData<*const (Fut, Ix, In, Im)>,
}

impl<S: Clone, F: Clone, Fut, Ix, In, Im> Clone for Map<S, F, Fut, Ix, In, Im> {
    fn clone(&self) -> Self {
        Self {
            svc: self.svc.clone(),
            fun: self.fun.clone(),
            tag: PhantomData,
        }
    }
}

impl<I, S, F, Fut, Ix, In, Im> Service<I> for Map<S, F, Fut, Ix, In, Im>
where
    S: Service<I> + Clone + 'static,

    F: Fn(In) -> Fut + Clone + 'static,

    Fut: Future<Output = Im>,

    <S as Service<I>>::Future: 'static,

    <S as Service<I>>::Response: Sculptor<In, Ix> + 'static,

    <<S as Service<I>>::Response as Sculptor<In, Ix>>::Remainder: Add<Im>,
{
    type Response =
        <<<S as Service<I>>::Response as Sculptor<In, Ix>>::Remainder as Add<Im>>::Output;

    type Error = <S as Service<I>>::Error;

    // TODO: is there any way to make this stack allocated?
    // * option 1: figure out a way to name the un-nameable type...
    // * option 2: use Pin<&mut dyn Future> or something and figure out lifetimes
    type Future = LocalBoxFuture<'static, Result<Self::Response, Self::Error>>;

    #[inline]
    fn poll_ready(&mut self, _: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    #[inline]
    fn call(&mut self, req: I) -> Self::Future {
        let mut svc = self.svc.clone();
        let fun = self.fun.clone();

        let fut = svc.call(req).and_then(|stack| async move {
            let (take, rest) = stack.sculpt();
            let merge = (fun)(take).await;
            Ok(rest + merge)
        });

        fut.boxed_local()
    }
}

#[derive(Copy, Debug)]
pub struct MapRef<S, F, Fut, Ix, In, Im> {
    svc: S,
    fun: F,
    tag: PhantomData<*const (Fut, Ix, In, Im)>,
}

impl<'b, S: Clone, F: Clone, Fut, Ix, In, Im> Clone for MapRef<S, F, Fut, Ix, In, Im> {
    fn clone(&self) -> Self {
        Self {
            svc: self.svc.clone(),
            fun: self.fun.clone(),
            tag: PhantomData,
        }
    }
}

impl<I, S, F, Fut, Ix, In, Im> Service<I> for MapRef<S, F, Fut, Ix, In, Im>
where
    S: Service<I> + Clone + 'static,

    F: Fn(In) -> Fut + Clone + 'static,

    Fut: Future<Output = Im>,

    <S as Service<I>>::Future: 'static,

    <S as Service<I>>::Response: for<'a> ToRef<'a> + Add<Im> + 'static,

    for<'a> <<S as Service<I>>::Response as ToRef<'a>>::Output: Sculptor<In, Ix>,
{
    type Response = <<S as Service<I>>::Response as Add<Im>>::Output;

    type Error = <S as Service<I>>::Error;

    // TODO: is there any way to make this stack allocated?
    // * option 1: figure out a way to name the un-nameable type...
    // * option 2: use Pin<&mut dyn Future> or something and figure out lifetimes
    type Future = LocalBoxFuture<'static, Result<Self::Response, Self::Error>>;

    #[inline]
    fn poll_ready(&mut self, _: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    #[inline]
    fn call(&mut self, req: I) -> Self::Future {
        let mut svc = self.svc.clone();
        let fun = self.fun.clone();

        let fut = svc.call(req).and_then(|stack| async move {
            let (take, _) = stack.to_ref().sculpt(); // this borrows for<'b>
            let merge = (fun)(take).await;

            Ok(stack + merge)
        });

        fut.boxed_local()
    }
}

#[test]
fn ensure_map_types_are_inferred() {
    struct A;
    struct B;
    struct C;
    struct D;
    struct E;
    struct F;
    struct G;

    async fn thing1(cx: Hlist![&B]) -> Hlist![D, E, &B] {
        hlist![D, E, cx.get()]
    }

    async fn thing2(cx: Hlist![&C, E, &B]) -> Hlist![F] {
        hlist![F]
    }

    async fn thing3(cx: Hlist![F, D, &A]) -> Hlist![] {
        hlist![]
    }

    async fn thing4(cx: Hlist![F, G, &A]) -> Hlist![] {
        hlist![]
    }

    let tree = Router::new(hlist![A, B, C])
        .subtree()
        .map(thing1)
        .map(thing2)
        .map(thing3)
        .collapse()
        .subtree()
        .map(thing1)
        .map(thing2)
        .map(|cx: Hlist![F, D, &A]| async { hlist![G, ...cx] })
        .map(|cx: Hlist![F, G]| async { cx })
        .map(thing4)
        // NOTE: intentionally inserted to break compilation here for experiments w/ errors
        // ------------------
        // E0282: consider giving this closure parameter a type
        //.map(|cx| cx)
        // ------------------
        // E0282: cannot infer type for type parameter `Ix` declared on the method `map`
        // help: consider specifying the type arguments in the method call: `map::<F, Fut, Ix, In, Im>`
        //.map(|cx| ready(cx))
        // -------------------
        // E0277: the trait `Plucker<F, _>` is not implemented for `HNil`
        //.map(|cx: Hlist![F, G]| async { hlist![] })
        // -------------------
        .collapse();
}

#[test]
fn ensure_map_ref_types_are_inferred() {
    struct A;
    struct B;
    struct C;
    struct D;
    struct E;
    struct F;
    struct G;

    async fn thing1(cx: Hlist![&&A]) -> Hlist![] {
        hlist![]
    }

    async fn thing2(cx: Hlist![]) -> Hlist![] {
        hlist![]
    }

    let tree = Router::new(hlist![A, B, C])
        .subtree()
        // TODO: any of these work on their own, but combine two and compilation fails....
        // WHY???
        //.map_ref(thing1)
        //.map_ref(thing1)
        //.map_ref(thing2)
        //.map_ref(|cx: Hlist![&&A, &&C]| async { hlist![] })
        .collapse();
}
