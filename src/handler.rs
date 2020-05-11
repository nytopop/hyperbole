use super::{
    combinators::{Add2, Base, Link},
    reply::Reply,
    tree::{Cluster, Params, Parser, PathSpec, Segment},
    Init, Response,
};
use frunk_core::{hlist, hlist::HNil};
use futures::future::{ready, BoxFuture, FutureExt, TryFutureExt};
use hyper::{
    header::{CONTENT_TYPE, X_CONTENT_TYPE_OPTIONS},
    Body, Request, StatusCode,
};
use std::{future::Future, marker::PhantomData, net::SocketAddr, ops::Add};

pub trait Handler: Sync + Send {
    fn handle(&self, req: Request<Body>, addr: SocketAddr) -> BoxFuture<'static, Response>;
}

#[derive(Copy, Clone)]
pub struct NotFound;

impl Handler for NotFound {
    fn handle(&self, _: Request<Body>, _: SocketAddr) -> BoxFuture<'static, Response> {
        ready(
            hyper::Response::builder()
                .status(StatusCode::NOT_FOUND)
                .header(CONTENT_TYPE, "text/plain; charset=utf-8")
                .header(X_CONTENT_TYPE_OPTIONS, "nosniff")
                .body("404 page not found".into())
                .unwrap(),
        )
        .boxed()
    }
}

pub struct HandlerFn<P, Fut> {
    fun: P,
    tag: PhantomData<fn(Fut)>,
}

impl<P: Fn(Request<Body>, SocketAddr) -> Fut, Fut> HandlerFn<P, Fut> {
    pub fn new(fun: P) -> Self {
        Self {
            fun,
            tag: PhantomData,
        }
    }
}

impl<P, Fut, Resp> Handler for HandlerFn<P, Fut>
where
    P: Fn(Request<Body>, SocketAddr) -> Fut + Sync + Send,
    Fut: Future<Output = Resp> + Send + 'static,
    Resp: Reply + 'static,
{
    fn handle(&self, req: Request<Body>, addr: SocketAddr) -> BoxFuture<'static, Response> {
        (self.fun)(req, addr).map(Reply::into_response).boxed()
    }
}

pub struct Chain<I, P, L> {
    state: I,
    path: PathSpec<P>,
    link: L,
}

impl<I: Clone, P, L: Clone> Clone for Chain<I, P, L> {
    fn clone(&self) -> Self {
        let state = self.state.clone();
        let path = self.path.clone();
        let link = self.link.clone();

        Self { state, path, link }
    }
}

impl<I: 'static, P: 'static, L: 'static> Handler for Chain<I, P, L>
where
    I: Sync + Send + Clone,
    P: Parser<Cluster>,
    L: Sync + Send + Link<Init<I>, P, Output = Response, Params = HNil>,
    <L as Link<Init<I>, P>>::Error: Reply,
{
    fn handle(&self, req: Request<Body>, addr: SocketAddr) -> BoxFuture<'static, Response> {
        let (p, body) = req.into_parts();

        let params = match self.path.parse_params(p.uri.path(), p.uri.query()) {
            Err(e) => return ready(e.into_response()).boxed(),
            Ok(ps) => ps,
        };

        let state = hlist![
            body,
            p.method,
            p.uri,
            p.version,
            p.headers,
            p.extensions,
            addr,
            ...self.state.clone()
        ];

        (self.link.handle_link(state, params))
            .map_ok(|(resp, _)| resp)
            .unwrap_or_else(Reply::into_response)
            .boxed()
    }
}

impl<I, P> Chain<I, P, Base> {
    pub const fn new(state: I, path: PathSpec<P>) -> Self {
        let link = Base;
        Self { state, path, link }
    }
}

impl<I, P, L> Chain<I, P, L> {
    pub fn link_next<Ln, F: FnOnce(L) -> Ln>(self, wrap: F) -> Chain<I, P, Ln> {
        let state = self.state;
        let path = self.path;
        let link = wrap(self.link);
        Chain { state, path, link }
    }

    pub fn add_path<_P>(self, spec: PathSpec<_P>) -> Chain<I, Add2<P, Params<_P>>, L>
    where
        P: Add<Params<_P>>,
        _P: Parser<Segment>,
    {
        let state = self.state;
        let path = self.path.append(spec);
        let link = self.link;
        Chain { state, path, link }
    }

    pub const fn path(&self) -> &PathSpec<P> {
        &self.path
    }
}
