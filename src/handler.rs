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
use std::{net::SocketAddr, ops::Add};

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

pub struct Chain<P, L> {
    path: PathSpec<P>,
    link: L,
}

impl<P, L: Clone> Clone for Chain<P, L> {
    fn clone(&self) -> Self {
        let path = self.path.clone();
        let link = self.link.clone();

        Self { path, link }
    }
}

impl<P: 'static, L: 'static> Handler for Chain<P, L>
where
    P: Parser<Cluster>,
    L: Sync + Send + Link<Init, P, Output = Response, Params = HNil>,
    <L as Link<Init, P>>::Error: Reply,
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
        ];

        (self.link.handle_link(state, params))
            .map_ok(|(resp, _)| resp)
            .unwrap_or_else(Reply::into_response)
            .boxed()
    }
}

impl<P> Chain<P, Base> {
    pub const fn new(path: PathSpec<P>) -> Self {
        Self { path, link: Base }
    }
}

impl<P, L> Chain<P, L> {
    pub fn link_next<Ln, F: FnOnce(L) -> Ln>(self, wrap: F) -> Chain<P, Ln> {
        let path = self.path;
        let link = wrap(self.link);
        Chain { path, link }
    }

    pub fn add_path<_P>(self, spec: PathSpec<_P>) -> Chain<Add2<P, Params<_P>>, L>
    where
        P: Add<Params<_P>>,
        _P: Parser<Segment>,
    {
        let path = self.path.append(spec);
        let link = self.link;
        Chain { path, link }
    }

    pub const fn path(&self) -> &PathSpec<P> {
        &self.path
    }
}
