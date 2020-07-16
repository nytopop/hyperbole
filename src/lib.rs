//! An experimental web framework based on functional generic programming.
#![feature(trait_alias, const_generics, type_alias_impl_trait)]
#![allow(incomplete_features, clippy::type_complexity)]
#![doc(test(
    no_crate_inject,
    attr(deny(rust_2018_idioms, unused_imports, unused_mut))
))]
#![warn(rust_2018_idioms, missing_docs)]

/// An attribute macro to reduce boilerplate when writing functions that accept an hlist as
/// an argument (handlers and middlewares).
///
/// This will translate the annotated function's argument list into an hlist. Any arguments
/// whose names start with underscores will be translated to their type, while all other
/// arguments will be translated to [named fields][field::Field] of their name and type.
///
/// # Examples
///
/// `fn f(a: u32, b: u32)` translates to `fn f(_: R![a: u32, b: u32])`.
///
/// `fn f(a: u32, _b: u32)` translates to `fn f(_: R![a: u32, u32])`.
///
/// ```
/// use hyperbole::{r, record_args, R};
///
/// #[record_args]
/// async fn my_func_a(first: u8, second: String, _third: Vec<u8>) {
///     // do stuff
/// }
///
/// # async fn call_my_func_a() {
/// // the translated function can be called using record syntax:
/// my_func_a(r![first = 4, second = "test-string".to_owned(), vec![
///     1, 2, 3
/// ]])
/// .await;
/// # }
///
/// // 'my_func_a' above is translated to something like this:
/// async fn my_func_b(cx: R![first: u8, second: String, Vec<u8>]) {
///     async fn my_func_b(first: u8, second: String, _third: Vec<u8>) {
///         // do stuff
///     }
///
///     my_func_b(
///         cx.head.into_inner(),
///         cx.tail.head.into_inner(),
///         cx.tail.tail.head,
///     )
///     .await
/// }
/// ```
pub use hyperbole_macros::record_args;

#[doc(hidden)]
pub use frunk_core;

pub mod body;
mod combinators;
pub mod field;
mod handler;
pub mod mw;
pub mod reply;
pub mod test;
pub mod tree;

use combinators::{
    Add2, Base, End, Inject, InjectAll, Link, Map, MapErr, MapErrs, Path, Then, TryMap, TryThen,
};
use handler::{Chain, Handler, NotFound};
use reply::Reply;
use tree::{Cluster, Node, Params, Parser, PathSpec, Route, Segment};

use frunk_core::{
    hlist::{HList, HNil},
    indices::Here,
};
use futures::future::{ready, BoxFuture, FutureExt, NeverError, Ready};
use http::{Extensions, HeaderMap, HeaderValue, Uri, Version};
use hyper::{
    header::LOCATION, server::conn::AddrStream, service::Service, Body, Method, Request, StatusCode,
};
use std::{
    borrow::Cow,
    collections::HashMap,
    convert::Infallible,
    future::Future,
    net::SocketAddr,
    ops::{Add, Deref},
    sync::Arc,
    task::{Context, Poll},
};

/// An http response.
pub type Response = hyper::Response<Body>;

#[doc(hidden)]
#[derive(Clone)]
pub struct AppDispatch(Arc<App>);

impl Service<&AddrStream> for AppDispatch {
    type Response = AppService;

    type Error = Infallible;

    type Future = NeverError<Ready<Self::Response>>;

    fn poll_ready(&mut self, _: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, tgt: &AddrStream) -> Self::Future {
        let svc = AppService {
            app: Arc::clone(&self.0),
            addr: tgt.remote_addr(),
        };

        ready(svc).never_error()
    }
}

#[doc(hidden)]
#[derive(Clone)]
pub struct AppService {
    app: Arc<App>,
    addr: SocketAddr,
}

impl Deref for AppService {
    type Target = App;

    fn deref(&self) -> &Self::Target {
        &self.app
    }
}

impl Service<Request<Body>> for AppService {
    type Response = Response;

    type Error = Infallible;

    type Future = NeverError<BoxFuture<'static, Response>>;

    fn poll_ready(&mut self, _: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, req: Request<Body>) -> Self::Future {
        self.dispatch(req, self.addr).never_error()
    }
}

/// The set of request scoped state that contexts are initialized with.
pub type Init = R![
    Body,
    Method,
    Uri,
    Version,
    HeaderMap<HeaderValue>,
    Extensions,
    SocketAddr,
];

/// Contains routes and handlers for a given http application.
///
/// # Examples
/// ```no_run
/// use hyper::{server::Server, Body};
/// use hyperbole::{uri, App, R};
///
/// #[tokio::main]
/// async fn main() -> hyper::Result<()> {
///     let app = App::new()
///         .context_path(uri!["first" / param: u32])
///         .map(|cx: R![param: _]| cx)
///         // GET /first/:param/echo
///         .get(uri!["echo"], |cx: R![param: _, Body]| async move {
///             let (param, body) = cx.into();
///             format!("param: {}, body: {:?}", param, body)
///         })
///         .collapse();
///
///     Server::bind(&([127, 0, 0, 1], 12345).into())
///         .serve(app.into_make_service())
///         .await
/// }
/// ```
pub struct App {
    // routes for common methods
    common: [Node<dyn Handler>; 9],
    // routes for custom methods
    custom: HashMap<Method, Node<dyn Handler>>,
    // 404 handler
    not_found: Box<dyn Handler>,
}

impl Default for App {
    fn default() -> Self {
        Self::new()
    }
}

impl App {
    /// Returns a new [App] with no handlers.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{f, zoom, App, R};
    ///
    /// let _app = App::new()
    ///     .context()
    ///     // &'static str will be available in this context
    ///     .inject("hello world")
    ///     .map(|cx: R![&str]| {
    ///         println!("str is {:?}", cx.get::<&str, _>());
    ///         cx
    ///     })
    ///     .map(|cx: R![&'static str]| cx)
    ///     .collapse();
    ///
    /// let _app = App::new()
    ///     .context()
    ///     // 'x: {integer}' will be available in this context
    ///     .inject(f![x = 40])
    ///     .map(|cx: R![x: u64]| {
    ///         println!("x is {}", zoom!(&cx.x));
    ///         cx
    ///     })
    ///     .collapse();
    /// ```
    pub fn new() -> Self {
        Self {
            common: Default::default(),
            custom: HashMap::new(),
            not_found: Box::new(NotFound),
        }
    }

    /// Begin a new request context at the provided base path. Any parameters parsed from the
    /// uri will be merged into the context's state.
    ///
    /// The [uri!] macro can be used to construct an appropriate [`PathSpec`].
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{uri, App};
    ///
    /// let _app = App::new()
    ///     // begin at /
    ///     .context_path(uri![])
    ///     .collapse()
    ///     // begin at /abc
    ///     .context_path(uri!["abc"])
    ///     .collapse()
    ///     // begin at /xyz/:param
    ///     .context_path(uri!["xyz" / param: u32])
    ///     .collapse();
    /// ```
    pub fn context_path<P: HList + Parser<Segment> + Send>(
        self,
        spec: PathSpec<P>,
    ) -> Ctx<Params<P>, Path<Base, P, Here>, App>
    {
        Ctx::with_source(self).path(spec)
    }

    /// Begin a new request context at the root path.
    pub fn context(self) -> Ctx<HNil, Base, App> {
        Ctx::with_source(self)
    }

    /// Configure a handler for the case where an incoming request does not match any existing
    /// routes.
    ///
    /// As in [Ctx::handle], the `handler` closure should accept an hlist argument, and return a
    /// future that evaluates to an http response (via the [Reply] trait).
    ///
    /// The argument hlist may consist of any subset of types from [Init].
    ///
    /// # Examples
    /// ```
    /// use hyper::{Method, StatusCode, Uri};
    /// use hyperbole::{record_args, reply::Reply, App};
    ///
    /// #[record_args]
    /// async fn handler(_m: Method, _u: Uri) -> impl Reply {
    ///     "not found".with_status(StatusCode::NOT_FOUND)
    /// }
    ///
    /// let _app = App::new().not_found(handler);
    /// ```
    pub fn not_found<F, Args, Ix, Fut, Resp>(mut self, handler: F) -> Self
    where
        F: Fn(Args) -> Fut + Sync + Send + 'static,
        Fut: Future<Output = Resp> + Send + 'static,
        Resp: Reply + 'static,
        End<Base, F, Args, Ix>: Link<Init, HNil, Output = Response, Params = HNil> + 'static,
    {
        let chain: Chain<HNil, End<Base, F, Args, Ix>> =
            Chain::new(uri![]).link_next(|link| End::new(link, handler));

        self.not_found = Box::new(chain);
        self
    }

    /// Consume this [App], turning it into a `MakeService` compatible with hyper servers.
    ///
    /// See [`hyper::server::Builder::serve`] for usage details.
    pub fn into_make_service(self) -> AppDispatch {
        AppDispatch(Arc::new(self))
    }

    fn get_node_mut(&mut self, method: Method) -> &mut Node<dyn Handler> {
        if let Some(i) = method_idx(&method) {
            &mut self.common[i]
        } else {
            self.custom.entry(method).or_default()
        }
    }

    fn lookup_route(&self, method: &Method, path: &str) -> Option<Route<'_, dyn Handler>> {
        method_idx(method)
            .map(|i| &self.common[i])
            .or_else(|| self.custom.get(method))
            .map(|n| n.lookup(path))
    }

    fn dispatch(&self, req: Request<Body>, addr: SocketAddr) -> BoxFuture<'static, Response> {
        #[inline]
        fn swap_trailing_slash(path: &str) -> Cow<'_, str> {
            if let Some(stripped) = path.strip_suffix('/') {
                return Cow::Borrowed(stripped);
            }

            let mut s = String::with_capacity(path.len() + 1);
            s.push_str(path);
            s.push('/');
            Cow::Owned(s)
        }

        let method = req.method();
        let path = req.uri().path();

        match self.lookup_route(method, path) {
            Some(Route { entry: Some(h), .. }) => h.handle(req, addr),

            Some(Route { tsr: true, .. }) if method != Method::CONNECT && path != "/" => {
                let code = if let Method::GET = *method {
                    StatusCode::MOVED_PERMANENTLY
                } else {
                    StatusCode::PERMANENT_REDIRECT
                };

                let resp = hyper::Response::builder()
                    .status(code)
                    .header(LOCATION, &*swap_trailing_slash(path))
                    .body(Body::empty())
                    .unwrap();

                Box::pin(async { resp })
            }

            _ => self.not_found.handle(req, addr),
        }
    }

    /// Create a test client for this app.
    pub fn test_client(self) -> test::Client {
        test::Client { app: self }
    }

    /// Merge route handlers into this [App].
    ///
    /// # Panics
    /// This method panics if any routes in `routes` conflict with a route in the [App].
    ///
    /// ```should_panic
    /// use hyperbole::{uri, App, Ctx, R};
    ///
    /// let routes = Ctx::default()
    ///     .get(uri!["conflict"], |_: R![]| async { "" })
    ///     .get(uri!["conflict"], |_: R![]| async { "" })
    ///     .into_routes();
    ///
    /// // 'a handler is already registered for path "/conflict"'
    /// let _app = App::new().merge(routes);
    /// ```
    ///
    /// ```should_panic
    /// use hyperbole::{uri, App, Ctx, R};
    ///
    /// let routes = Ctx::default()
    ///     .get(uri!["something"], |_: R![]| async { "" })
    ///     .get(uri![param: u32], |_: R![]| async { "" })
    ///     .into_routes();
    ///
    /// // 'wildcard ":param" conflicts with existing children in path "/:param"'
    /// let _app = App::new().merge(routes);
    /// ```
    pub fn merge(mut self, routes: Routes) -> Self {
        for r in routes.inner {
            self.get_node_mut(r.method).insert(&r.path, r.handler);
        }
        self
    }
}

#[inline]
fn method_idx(m: &Method) -> Option<usize> {
    Some(match *m {
        Method::GET => 0,
        Method::POST => 1,
        Method::PUT => 2,
        Method::DELETE => 3,
        Method::HEAD => 4,
        Method::OPTIONS => 5,
        Method::CONNECT => 6,
        Method::PATCH => 7,
        Method::TRACE => 8,
        _ => return None,
    })
}

/// A request processing context.
///
/// In effect, this represents a cumulative builder-pattern constructor for request handlers.
///
/// # Strongly typed request scoped state
/// The core abstraction used within this struct is an hlist of request scoped state paired with a
/// composable chain of middlewares that transform it.
///
/// Each [Ctx] state starts life as an [Init], and is modified through successive application of
/// various middleware combinators (such as [map], [then], [try_map], [path], etc).
///
/// ```
/// use hyper::Uri;
/// use hyperbole::{Ctx, R, r};
///
/// let _ctx = Ctx::default()
///     // a no-op middleware which doesn't modify the state
///     .map(|cx: R![]| cx)
///     // a middleware that adds a `usize` to the state, based on the uri
///     .map(|cx: R![Uri]| r![cx.head.path().len(), ...cx])
///     // a middlware that consumes the uri, and adds nothing
///     .map(|cx: R![Uri]| r![]);
/// ```
///
/// # Handling requests
/// At any point, a handler function may be registered for a given route. The handler will execute
/// after any middlewares that have been composed prior to it, and will likewise have access to any
/// of the accumulated state.
///
/// New middlewares do not retroactively apply to handlers that have already been registered. Only
/// the middlewares logically prior to a handler's registration will be folded into that handler.
///
/// Unlike middlewares - which return new state - handlers should return a value which implements
/// [Reply].
///
/// ```
/// use hyperbole::{r, uri, Ctx, R};
///
/// let _ctx = Ctx::default()
///     .map(|_: R![]| r!["hello worldo"])
///     // only the above `map` is executed before this handler
///     .get(uri!["some-route"], |cx: R![&str]| async move {
///         format!("message: {:?}", cx.head)
///     })
///     .map(|_: R![]| r![3.14159])
///     // but this handler is preceded by both `map`s
///     .get(uri!["another"], |cx: R![&str, f64]| async move {
///         format!("message: {:?}, number: {}", cx.head, cx.tail.head)
///     });
/// ```
///
/// # Parsing request uris
/// Parameters in uris can be described with the [uri!] macro. Much like middlewares, path parsers
/// merge new elements into the request scoped state.
///
/// ```
/// use hyperbole::{r, record_args, uri, Ctx, R};
///
/// #[derive(Debug)]
/// struct Widget;
///
/// #[record_args]
/// fn retrieve_widget(widget_id: u64) -> R![Widget] {
///     r![Widget]
/// }
///
/// let _widget_ctx = Ctx::default()
///     .path(uri!["widgets" / widget_id: u64])
///     .map(retrieve_widget)
///     .get(uri!["show"], |cx: R![Widget]| async move {
///         format!("{:?}", cx.head)
///     });
/// ```
///
/// # Error handling and flow control
/// Errors that arise during request resolution are represented in the context as [coproducts] (a
/// generalization of enums). When a fallible middleware is used ([try_map] or [try_then]), an
/// additional error variant is added to the context's error coproduct. This also applies to parse
/// errors of dynamic path parameters (which are wrapped in a [tree::UriError]).
///
/// If a fallible middleware returns `Err`, the request being processed short circuits and cannot
/// be recovered. The specific error response returned to the client can however be modified by
/// [map_errs] or [map_err]. The former transforms the complete error coproduct, while the latter
/// maps over a single variant.
///
/// ```
/// use hyperbole::{record_args, tree::UriError, uri, Ctx, R};
/// use std::num::ParseIntError;
///
/// #[derive(Debug)]
/// struct Widget;
///
/// #[record_args]
/// fn retrieve_widget(widget_id: u64) -> Result<R![Widget], &'static str> {
///     Err("bad news")
/// }
///
/// let _widget_ctx = Ctx::default()
///     .path(uri!["widgets" / widget_id: u64])
///     .try_map(retrieve_widget)
///     .map_err(|e: UriError<ParseIntError>| {
///         println!("failed to parse {:?} as a u64: {}", e.item, e.err);
///         e
///     })
///     .map_err(|e: &str| {
///         println!("failed to retrieve widget: {}", e);
///         e
///     })
///     .get(uri!["show"], |cx: R![Widget]| async move {
///         format!("{:?}", cx.head)
///     });
/// ```
///
/// # Limitations
/// Due to the extensive use of type inference to extract subsets of the request scoped state, the
/// state may not contain duplicate instances of a type. That is, it is a *set*, and not a *list*.
///
/// This property arises without explicit enforcement; type inference will simply begin failing if
/// duplicate types are encountered.
///
/// ```compile_fail,E0282
/// use hyperbole::{r, Ctx, R};
///
/// struct A(u32);
///
/// let _ctx = Ctx::default()
///     // merge an A
///     .map(|cx: R![]| r![A(1)])
///     // merge an A (state now contains two `A`s)
///     .map(|cx: R![]| r![A(2)])
///     // this fails during type inference, because it's ambiguous _which_ A we want
///     //
///     // error[E0282]: type annotations needed
///     //     cannot infer type for type parameter `TailIndex`
///     .map(|cx: R![A]| cx);
/// ```
///
/// [Named fields] can be used to disambiguate between what would otherwise be duplicate types. In
/// particular, the [uri!] macro takes advantage of this to allow multiple instances of common
/// primitive types like `u32` or `String` to be extracted from a uri.
///
/// The above example can be rewritten using named fields to avoid the inference failure:
///
/// ```
/// use hyperbole::{r, Ctx, R};
///
/// struct A(u32);
///
/// let _ctx = Ctx::default()
///     .map(|cx: R![]| r![first = A(1)])
///     .map(|cx: R![]| r![second = A(2)])
///     // we want the A called 'second'
///     .map(|cx: R![second: A]| cx)
///     // we want the A called 'first'
///     .map(|cx: R![first: A]| cx)
///     // we want both of them
///     .map(|cx: R![first: A, second: A]| cx);
/// ```
///
/// [map]: Ctx::map
/// [then]: Ctx::then
/// [try_map]: Ctx::try_map
/// [try_then]: Ctx::try_then
/// [map_err]: Ctx::map_err
/// [map_errs]: Ctx::map_errs
/// [path]: Ctx::path
/// [coproducts]: frunk_core::coproduct
/// [Named fields]: field::Field
pub struct Ctx<P, L, S = ()> {
    source: S,
    routes: Vec<RouteEntry>,
    chain: Chain<P, L>,
}

macro_rules! handle {
    ($( [$name:ident, $method:path] ),+) => {
        $(handle! {@withdoc
            concat!(
                "A convenience method to call [handle][Ctx::handle] with ",
                stringify!([$method].),
            ),
            $name,
            $method,
        })+
    };

    (@withdoc $desc:expr, $name:ident, $method:path $(,)?) => {
        #[doc = $desc]
        pub fn $name<_P, F, Args, Ix, Pix, Fut, Resp>(self, spec: PathSpec<_P>, handler: F) -> Self
        where
            F: Fn(Args) -> Fut + Sync + Send,
            Fut: Future<Output = Resp> + Send,
            Resp: Reply ,
            (): CtxState2<L, P, _P, Pix, F, Args, Ix>,
        {
            self.handle($method, spec, handler)
        }
    };
}

macro_rules! handle_with {
    ($( [$name:ident, $method:path] ),+) => {
        $(handle_with! {@withdoc
            concat!(
                "A convenience method to call [handle_with][Ctx::handle_with] with ",
                stringify!([$method].),
            ),
            $name,
            $method,
        })+
    };

    (@withdoc $desc:expr, $name:ident, $method:path $(,)?) => {
        #[doc = $desc]
        pub fn $name<_P, Pix, W, WArgs, WFut, Merge, E, Wix, F, Args, Fut, Resp, Ix>(
            self,
            spec: PathSpec<_P>,
            with: W,
            handler: F,
        ) -> Self
        where
            W: Fn(WArgs) -> WFut + Sync + Send,
            WFut: Future<Output = Result<Merge, E>> + Send,
            E: Reply,

            F: Fn(Args) -> Fut + Sync + Send,
            Fut: Future<Output = Resp> + Send,
            Resp: Reply,

            (): CtxState3<L, P, _P, Pix, W, WArgs, Wix, F, Args, Ix>,
        {
            self.handle_with($method, spec, with, handler)
        }
    };
}

impl Default for Ctx<HNil, Base> {
    fn default() -> Self {
        Self::with_source(())
    }
}

impl<S> Ctx<HNil, Base, S> {
    fn with_source(source: S) -> Self {
        Self {
            source,
            routes: vec![],
            chain: Chain::new(uri![]),
        }
    }
}

impl<P: HList + Send + Parser<Segment>> Ctx<Params<P>, Path<Base, P, Here>> {
    /// Create a new request context at the provided base path. Any parameters parsed from the
    /// uri will be merged into the context's state.
    ///
    /// The [uri!] macro can be used to construct an appropriate [`PathSpec`].
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{r, uri, Ctx, R};
    ///
    /// let _ctx = Ctx::with_path(uri!["foo" / "bar" / baz: f64])
    ///     .map(|cx: R![baz: _]| r![qux = *cx.head > 3.14159265])
    ///     .map(|cx: R![qux: _]| cx);
    /// ```
    pub fn with_path(spec: PathSpec<P>) -> Self {
        Ctx::default().path(spec)
    }
}

impl<T: Clone> Ctx<HNil, InjectAll<Base, T>>
where InjectAll<Base, T>: Link<Init, HNil>
{
    /// Create a new request context with an hlist of cloneable values. All elements of `values`
    /// will be merged into the context's state.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{r, Ctx, R};
    ///
    /// let _ctx = Ctx::with_state(r![x = 4, y = "hello", z = "world"])
    ///     .map(|cx: R![x: _]| cx)
    ///     .map(|cx: R![y: _, z: _]| cx)
    ///     .map(|cx: R![z: _, x: _, y: _]| cx);
    /// ```
    pub fn with_state(values: T) -> Self {
        Ctx::default().inject_all(values)
    }
}

impl<P: 'static, L: Sync + Send + Clone + 'static, S> Ctx<P, L, S> {
    fn link_next<Ln, F: FnOnce(L) -> Ln>(self, wrap: F) -> Ctx<P, Ln, S> {
        Ctx {
            source: self.source,
            routes: self.routes,
            chain: self.chain.link_next(wrap),
        }
    }

    /// Inject a cloneable value into the request scoped state.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{f, r, Ctx, R};
    ///
    /// let _ctx = Ctx::default()
    ///     .inject("just an &str")
    ///     .map(|cx: R![&str]| r![])
    ///     .inject(f![xyz = "this is a named field"])
    ///     .map(|cx: R![xyz: _]| r![]);
    /// ```
    pub fn inject<T: Clone>(self, value: T) -> Ctx<P, Inject<L, T>, S>
    where Inject<L, T>: Link<Init, P> {
        self.link_next(|link| Inject::new(link, value))
    }

    /// Inject an hlist of cloneable values into the request scoped state.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{r, Ctx, R};
    ///
    /// let _ctx = Ctx::default()
    ///     .inject_all(r![a = "foobar", b = 42])
    ///     .map(|cx: R![b: _, a: _]| cx)
    ///     .inject_all(r![c = ()])
    ///     .map(|cx: R![a: _, b: _, c: _]| cx);
    /// ```
    pub fn inject_all<T: Clone>(self, values: T) -> Ctx<P, InjectAll<L, T>, S>
    where InjectAll<L, T>: Link<Init, P> {
        self.link_next(|link| InjectAll::new(link, values))
    }

    /// Transform a subset of the request scoped state with a closure.
    ///
    /// The provided closure should accept an hlist argument, and return an hlist.
    ///
    /// The argument hlist may consist of any subset of types that are present within the context's
    /// state up to this point. Each element will be removed from the context's state and *moved*
    /// into `f` upon execution (making them inaccessible to subsequent middlewares and handlers).
    ///
    /// Likewise, any types in the returned hlist will be *moved* into the context's state.
    ///
    /// # Examples
    /// ```
    /// use hyper::Body;
    /// use hyperbole::{r, record_args, Ctx, R};
    ///
    /// #[record_args]
    /// fn fun(_: Body, _: u32) -> R![] {
    ///     r![]
    /// }
    ///
    /// let _ctx = Ctx::default()
    ///     .map(|cx: R![Body]| cx)
    ///     .map(|cx: R![]| r![12345])
    ///     .map(fun);
    /// ```
    pub fn map<F, Args, Ix, Merge>(self, f: F) -> Ctx<P, Map<L, F, Args, Ix>, S>
    where
        F: Fn(Args) -> Merge,
        Merge: HList,
        Map<L, F, Args, Ix>: Link<Init, P>,
    {
        self.link_next(|link| Map::new(link, f))
    }

    /// Transform a subset of the request scoped state with a fallible closure.
    ///
    /// The provided closure should accept an hlist argument, and return an hlist in a [Result]
    /// (where the error type implements [Reply]).
    ///
    /// The argument hlist may consist of any subset of types that are present within the context's
    /// state up to this point. Each element will be removed from the context's state and *moved*
    /// into `f` upon execution (making them inaccessible to subsequent middlewares and handlers).
    ///
    /// If the closure returns `Ok`, any types in the returned hlist will be *moved* into the
    /// context's state.
    ///
    /// If the closure returns `Err`, the request will short circuit with a response created via
    /// the error's [Reply] implementation.
    ///
    /// For subsequent combinators, the context's error type will contain an additional variant for
    /// `E`.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{uri, zoom, Ctx, R};
    ///
    /// let _ctx = Ctx::with_path(uri![a: u32 / b: u32])
    ///     .try_map(|cx: R![a: _, b: _]| match zoom!(&cx.a) > zoom!(&cx.b) {
    ///         false => Err("uh oh"),
    ///         true => Ok(cx),
    ///     })
    ///     .map_err(|e: &str| "e is the above error, if it happened");
    /// ```
    pub fn try_map<F, Args, Ix, Merge, E>(self, f: F) -> Ctx<P, TryMap<L, F, Args, Ix>, S>
    where
        F: Fn(Args) -> Result<Merge, E>,
        Merge: HList,
        E: Reply,
        TryMap<L, F, Args, Ix>: Link<Init, P>,
    {
        self.link_next(|link| TryMap::new(link, f))
    }

    /// Transform a subset of the request scoped state with a closure that returns a future.
    ///
    /// The provided closure should accept an hlist argument, and return a future that evaluates
    /// to an hlist.
    ///
    /// The argument hlist may consist of any subset of types that are present within the context's
    /// state up to this point. Each element will be removed from the context's state and *moved*
    /// into `f` upon execution (making them inaccessible to subsequent middlewares and handlers).
    ///
    /// Likewise, any types in the returned hlist will be *moved* into the context's state.
    ///
    /// # Examples
    /// ```
    /// use hyper::Body;
    /// use hyperbole::{r, record_args, Ctx, R};
    ///
    /// #[record_args]
    /// async fn fun(_: Body) -> R![] {
    ///     r![]
    /// }
    ///
    /// let _ctx = Ctx::default()
    ///     .then(|cx: R![Body]| async move { cx })
    ///     .then(|cx: R![]| async move { cx })
    ///     .then(fun);
    /// ```
    pub fn then<F, Args, Ix, Fut, Merge>(self, f: F) -> Ctx<P, Then<L, F, Args, Ix>, S>
    where
        F: Fn(Args) -> Fut,
        Fut: Future<Output = Merge>,
        Merge: HList,
        Then<L, F, Args, Ix>: Link<Init, P>,
    {
        self.link_next(|link| Then::new(link, f))
    }

    /// Transform a subset of the request scoped state with a closure that returns a fallible
    /// future.
    ///
    /// The provided closure should accept an hlist argument, and return a future that evaluates to
    /// an hlist in a [Result] (where the error type implements [Reply]).
    ///
    /// The argument hlist may consist of any subset of types that are present within the context's
    /// state up to this point. Each element will be removed from the context's state and *moved*
    /// into `f` upon execution (making them inaccessible to subsequent middlewares and handlers).
    ///
    /// If the future evaluates to `Ok`, any types in the returned hlist will be *moved* into the
    /// context's state.
    ///
    /// If the future evaluates to `Err`, the request will short circuit with a response created
    /// via the error's [Reply] implementation.
    ///
    /// For subsequent combinators, the context's error type will contain an additional variant for
    /// `E`.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{r, uri, Ctx, R};
    ///
    /// let _ctx = Ctx::with_path(uri![a: f64 / b: String])
    ///     .try_then(|cx: R![a: f64, b: String]| async move {
    ///         let (a, b) = cx.into();
    ///         if *a == 3.14159265 && *b != "blue" {
    ///             Err("always blue!")
    ///         } else {
    ///             Ok(r![color = "it was blue!"])
    ///         }
    ///     })
    ///     .map(|cx: R![color: _]| cx);
    /// ```
    pub fn try_then<F, Args, Ix, Fut, Merge, E>(self, f: F) -> Ctx<P, TryThen<L, F, Args, Ix>, S>
    where
        F: Fn(Args) -> Fut,
        Fut: Future<Output = Result<Merge, E>>,
        Merge: HList,
        E: Reply,
        TryThen<L, F, Args, Ix>: Link<Init, P>,
    {
        self.link_next(|link| TryThen::new(link, f))
    }

    /// Transform the context's error type with a closure.
    ///
    /// The error will be a [Coproduct] with a variant for all potential error cases so far.
    ///
    /// Any [Coproduct] may be returned, so long as any variants it contains all implement [Reply].
    ///
    /// # Examples
    /// ```
    /// use frunk_core::Coprod;
    /// use hyperbole::{Ctx, R};
    ///
    /// let _ctx = Ctx::default()
    ///     // without any fallible combinators, the error is an uninhabitable enum:
    ///     .map_errs(|err: Coprod![]| -> Coprod![] { match err {} })
    ///     .map(|cx: R![]| cx);
    /// ```
    ///
    /// [Coproduct]: frunk_core::coproduct::Coproduct
    pub fn map_errs<F, E>(self, f: F) -> Ctx<P, MapErrs<L, F>, S>
    where
        F: Fn(<L as Link<Init, P>>::Error) -> E,
        E: Reply,
        L: Link<Init, P>,
        MapErrs<L, F>: Link<Init, P>,
    {
        self.link_next(|link| MapErrs::new(link, f))
    }

    /// Transform a single variant of the context's error type with a closure.
    ///
    /// This can be used to selectively modify only a single type of error. Note that if more than
    /// one instance of the same error may have occurred, this will only affect the most recent of
    /// them.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{record_args, Ctx, R};
    ///
    /// fn fallible_a(_: R![]) -> Result<R![], String> {
    ///     Err("uh oh".to_owned())
    /// }
    ///
    /// #[record_args]
    /// fn fallible_b() -> Result<R![], Vec<u8>> {
    ///     Err(b"uh oh".to_vec())
    /// }
    ///
    /// let _ctx = Ctx::default()
    ///     .try_map(fallible_a)
    ///     .try_map(fallible_b)
    ///     .map_err(|e: String| "it was String")
    ///     .map_err(|e: Vec<u8>| "it was Vec<u8>");
    /// ```
    pub fn map_err<F, E, Ix, R>(self, f: F) -> Ctx<P, MapErr<L, F, E, Ix>, S>
    where
        F: Fn(E) -> R,
        R: Reply,
        MapErr<L, F, E, Ix>: Link<Init, P>,
    {
        self.link_next(|link| MapErr::new(link, f))
    }

    /// Append additional path segments to this context's base path. Any new parameters parsed from
    /// the uri will be merged into the context's state at this point.
    ///
    /// The [uri!] macro can be used to construct an appropriate [`PathSpec`].
    ///
    /// When a request is being handled, the concatenated path specification is parsed before any
    /// middlewares execute. However, all extracted parameters (and parsing errors) are deferred
    /// such that they only appear at the point where they were specified.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{tree::UriError, uri, Ctx, R};
    /// use std::num::ParseFloatError;
    ///
    /// let _ctx = Ctx::default()
    ///     .path(uri!["first" / x: usize / y: f64])
    ///     .map(|cx: R![x: _]| cx)
    ///     .map_err(|e: UriError<ParseFloatError>| e.item)
    ///     .map(|cx: R![y: _]| cx)
    ///     .map(|cx: R![x: _, y: _]| cx)
    ///     // GET /first/:x/:y/abc
    ///     .get(uri!["abc"], |cx: R![x: _, y: _]| async { "" });
    /// ```
    pub fn path<_P, Ix>(self, spec: PathSpec<_P>) -> Ctx<Add2<P, Params<_P>>, Path<L, _P, Ix>, S>
    where
        P: Add<Params<_P>>,
        _P: Parser<Segment>,
        Path<L, _P, Ix>: Link<Init, Add2<P, Params<_P>>>,
    {
        Ctx {
            source: self.source,
            routes: self.routes,
            chain: self.chain.add_path(spec).link_next(Path::new),
        }
    }

    /// Register a request handler for this context's base path with `spec` appended to it.
    ///
    /// The provided `handler` closure should accept an hlist argument, and return a future that
    /// evaluates to an http response (via the [Reply] trait).
    ///
    /// The argument hlist may consist of any subset of types that are present within the context's
    /// state up to this point, or any parameters parsed from the provided path `spec`.
    ///
    /// If an incoming request matches this route, every middleware accumulated in the context up
    /// to this point will execute. Assuming none of them short circuit with an error, this handler
    /// will then be executed.
    ///
    /// # Examples
    /// ```
    /// use hyper::Body;
    /// use hyperbole::{r, record_args, reply::Reply, uri, Ctx, R};
    ///
    /// #[record_args]
    /// async fn doit(baz: f64) -> &'static str {
    ///     "&'static str implements Reply"
    /// }
    ///
    /// async fn more(cx: R![Body, u32]) -> &'static [u8] {
    ///     b"so does &'static [u8]"
    /// }
    ///
    /// async fn using_impl(cx: R![]) -> impl Reply {
    ///     vec![1, 2, 3, 4, 5]
    /// }
    ///
    /// let _ctx = Ctx::with_path(uri!["foo" / "bar" / baz: f64])
    ///     .get(uri!["doit"], doit)
    ///     .map(|cx: R![baz: _]| r![15])
    ///     .get(uri!["more"], more)
    ///     .get(uri!["more" / neat: u32], more)
    ///     .get(uri!["more" / neat: u32 / "nested"], more)
    ///     .get(uri!["impl_reply"], using_impl);
    /// ```
    pub fn handle<_P, F, Args, Ix, Pix, Fut, Resp>(
        mut self,
        method: Method,
        spec: PathSpec<_P>,
        handler: F,
    ) -> Self
    where
        F: Fn(Args) -> Fut + Sync + Send,
        Fut: Future<Output = Resp> + Send,
        Resp: Reply,
        (): CtxState2<L, P, _P, Pix, F, Args, Ix>,
    {
        let chain = (self.chain.clone())
            .add_path(spec)
            .link_next(|link| -> Path<_, _P, Pix> { Path::new(link) })
            .link_next(|link| -> End<_, F, Args, Ix> { End::new(link, handler) });

        self.routes.push(RouteEntry {
            method,
            path: format!("{}", chain.path()),
            handler: Box::new(chain),
        });

        self
    }

    handle!(
        [get, Method::GET],
        [post, Method::POST],
        [put, Method::PUT],
        [patch, Method::PATCH],
        [delete, Method::DELETE]
    );

    /// Register a request handler for this context's base path with `spec` appended to it.
    ///
    /// The semantics of this are mostly equivalent to [handle], except for an additional `with`
    /// argument, which should be a closure that could be passed to [try_then]. It will behave as
    /// if added between the path combinator and handler (that is, it has access to any new types
    /// introduced in `spec`, and merges types accessible to `handler`).
    ///
    /// This is useful for specifying a different request body parser for multiple handlers that
    /// otherwise share the same chain of middlewares.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{body::jsonr, record_args, uri, Ctx, R};
    ///
    /// async fn handle_abc(cx: R![a: u32, b: String, c: f64]) -> &'static str {
    ///     "neat"
    /// }
    ///
    /// #[record_args]
    /// async fn handle_cba(c: f64, b: String, a: u32) -> &'static str {
    ///     "neat"
    /// }
    ///
    /// let _ctx = Ctx::default()
    ///     .get_with(uri!["1" / a: u32], jsonr::<R![b: _, c: _]>, handle_abc)
    ///     .get_with(uri!["2" / a: u32], jsonr::<R![b: _, c: _]>, handle_cba);
    /// ```
    ///
    /// [handle]: Ctx::handle
    /// [try_then]: Ctx::try_then
    pub fn handle_with<_P, Pix, W, WArgs, WFut, Merge, E, Wix, F, Args, Fut, Resp, Ix>(
        mut self,
        method: Method,
        spec: PathSpec<_P>,
        with: W,
        handler: F,
    ) -> Self
    where
        W: Fn(WArgs) -> WFut + Sync + Send,
        WFut: Future<Output = Result<Merge, E>> + Send,
        E: Reply,

        F: Fn(Args) -> Fut + Sync + Send,
        Fut: Future<Output = Resp> + Send,
        Resp: Reply,

        (): CtxState3<L, P, _P, Pix, W, WArgs, Wix, F, Args, Ix>,
    {
        let chain = (self.chain.clone())
            .add_path(spec)
            .link_next(|link| -> Path<_, _P, Pix> { Path::new(link) })
            .link_next(|link| -> TryThen<_, W, WArgs, Wix> { TryThen::new(link, with) })
            .link_next(|link| -> End<_, F, Args, Ix> { End::new(link, handler) });

        self.routes.push(RouteEntry {
            method,
            path: format!("{}", chain.path()),
            handler: Box::new(chain),
        });

        self
    }

    handle_with!(
        [get_with, Method::GET],
        [post_with, Method::POST],
        [put_with, Method::PUT],
        [patch_with, Method::PATCH],
        [delete_with, Method::DELETE]
    );

    /// Collapse this context and retrieve any routes registered via [handle] (or helpers like
    /// [get], [post], etc).
    ///
    /// [handle]: Ctx::handle
    /// [get]: Ctx::get
    /// [post]: Ctx::post
    pub fn into_routes(self) -> Routes {
        Routes { inner: self.routes }
    }
}

impl<P: 'static, L: Sync + Send + Clone + 'static> Ctx<P, L, App> {
    /// Collapse this context and return to the base [App].
    ///
    /// This discards any accumulated combinators and path specifications, while retaining handlers
    /// registered via [handle] (or helpers like [get], [post], etc).
    ///
    /// # Panics
    /// This method panics if any registered handler paths (with the same method) conflict with
    /// eachother or any routes in the [App].
    ///
    /// ```should_panic
    /// use hyperbole::{uri, App, R};
    ///
    /// // 'a handler is already registered for path "/conflict"'
    /// let _app = App::new()
    ///     .context()
    ///     .get(uri!["conflict"], |_: R![]| async { "" })
    ///     .get(uri!["conflict"], |_: R![]| async { "" })
    ///     .collapse();
    /// ```
    ///
    /// ```should_panic
    /// use hyperbole::{uri, App, R};
    ///
    /// // 'wildcard ":param" conflicts with existing children in path "/:param"'
    /// let _app = App::new()
    ///     .context()
    ///     .get(uri!["something"], |_: R![]| async { "" })
    ///     .get(uri![param: u32], |_: R![]| async { "" })
    ///     .collapse();
    /// ```
    ///
    /// [handle]: Ctx::handle
    /// [get]: Ctx::get
    /// [post]: Ctx::post
    pub fn collapse(self) -> App {
        self.source.merge(Routes { inner: self.routes })
    }
}

#[doc(hidden)]
pub trait CtxState2<L, P, _P, Pix, F, Args, Ix> = where
    P: Add<Params<_P>>,
    _P: Parser<Segment>,
    Add2<P, Params<_P>>: Parser<Cluster>,
    End<Path<L, _P, Pix>, F, Args, Ix>:
        Link<Init, Add2<P, Params<_P>>, Output = Response, Params = HNil> + 'static;

#[doc(hidden)]
pub trait CtxState3<L, P, _P, Pix, W, WArgs, Wix, F, Args, Ix> = where
    P: Add<Params<_P>>,
    _P: Parser<Segment>,
    Add2<P, Params<_P>>: Parser<Cluster>,
    End<TryThen<Path<L, _P, Pix>, W, WArgs, Wix>, F, Args, Ix>:
        Link<Init, Add2<P, Params<_P>>, Output = Response, Params = HNil> + 'static;

/// A collection of route handlers.
pub struct Routes {
    inner: Vec<RouteEntry>,
}

struct RouteEntry {
    method: Method,
    path: String,
    handler: Box<dyn Handler>,
}
