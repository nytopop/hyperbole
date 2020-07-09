//! An experimental web framework based on functional generic programming.
#![feature(trait_alias, const_generics, type_alias_impl_trait)]
#![allow(incomplete_features, clippy::type_complexity)]
#![doc(test(
    no_crate_inject,
    attr(deny(rust_2018_idioms, unused_imports, unused_mut))
))]
#![warn(rust_2018_idioms, missing_docs)]

#[doc(inline)]
pub use frunk_core::{coproduct, hlist, Coprod, Hlist};

/// An attribute macro to reduce boilerplate when writing functions that accept an hlist as
/// an argument (handlers and middlewares).
///
/// This will translate the annotated function's argument list into an hlist. Any arguments
/// whose names start with underscores will be translated to their type, while all other
/// arguments will be translated to [named fields][field::Field] of their name and type.
///
/// # Examples
///
/// `fn f(a: u32, b: u32)` translates to `fn f(_: Hlist![f![a: u32], f![b: u32]])`.
///
/// `fn f(a: u32, _b: u32)` translates to `fn f(_: Hlist![f![a: u32], u32])`.
///
/// ```
/// use hyperbole::{f, hlist, record, record_args, Hlist};
///
/// #[record_args]
/// async fn my_func_a(first: u8, second: String, _third: Vec<u8>) {
///     // do stuff
/// }
///
/// async fn call_my_func_a() {
///     // the translated function can be called using record syntax:
///     my_func_a(record![first = 4, second = "test-string".to_owned(), [
///         vec![1, 2, 3]
///     ]])
///     .await;
///
///     // or desugared hlist syntax:
///     my_func_a(hlist![4.into(), "test-string".to_owned().into(), vec![
///         1, 2, 3
///     ]])
///     .await;
/// }
///
/// // 'my_func_a' above is translated to something like this:
/// async fn my_func_b(cx: Hlist![f![first: u8], f![second: String], Vec<u8>]) {
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
    coproduct::{CNil, Coproduct},
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
pub type Init = Hlist![
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
/// use hyperbole::{path, record, App};
///
/// #[tokio::main]
/// async fn main() -> hyper::Result<()> {
///     let app = App::new()
///         .context_path(path!["first" / param: u32])
///         .map(|cx: record![param]| cx)
///         // GET /first/:param/echo
///         .get(path!["echo"], |cx: record![param, [Body]]| async move {
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

impl App {
    /// Returns a new [App] with no handlers.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{access, f, record, App, Hlist};
    ///
    /// let _app = App::new()
    ///     .context()
    ///     // &'static str will be available in this context
    ///     .inject("hello world")
    ///     .map(|cx: Hlist![&str]| {
    ///         println!("str is {:?}", cx.get::<&str, _>());
    ///         cx
    ///     })
    ///     .map(|cx: Hlist![&'static str]| cx)
    ///     .collapse();
    ///
    /// let _app = App::new()
    ///     .context()
    ///     // 'x: {integer}' will be available in this context
    ///     .inject(f![x = 40])
    ///     .map(|cx: record![x: u64]| {
    ///         println!("x is {}", access!(&cx.x));
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
    /// The [path!] macro can be used to construct an appropriate [`PathSpec`].
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{path, App};
    ///
    /// let _app = App::new()
    ///     // begin at /
    ///     .context_path(path![])
    ///     .collapse()
    ///     // begin at /abc
    ///     .context_path(path!["abc"])
    ///     .collapse()
    ///     // begin at /xyz/:param
    ///     .context_path(path!["xyz" / param: u32])
    ///     .collapse();
    /// ```
    pub fn context_path<P: Parser<Segment>>(
        self,
        spec: PathSpec<P>,
    ) -> Ctx<Params<P>, Path<Base, P, Here>>
    {
        let spec = PathSpec::ROOT.append(spec);
        let chain = Chain::new(spec).link_next(Path::new);

        Ctx { app: self, chain }
    }

    /// Begin a new request context at the root path.
    pub fn context(self) -> Ctx<Params<HNil>, Path<Base, HNil, Here>> {
        self.context_path(PathSpec::ROOT)
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
            Chain::new(path![]).link_next(|link| End::new(link, handler));

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
    #[inline]
    pub fn test_client(self) -> test::Client {
        test::Client { app: self }
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
/// It can be thought of as a composable chain of partial transformations over an hlist of
/// request scoped values; a lazily declarative specification of 'how to process a request'.
///
/// Much like [Iterator], a context by itself doesn't really *do* anything (it is dropped by
/// the time requests are being processed). It exists only to construct request handlers for
/// registration as routes in an [App].
///
/// Each context tracks two hlists and a combinator chain that transforms them:
///
/// 1. An hlist generated from incoming http request parts.
/// 2. An hlist of parameters parsed from request uris.
///
/// See [Init] for the exact set of initial state available in fresh contexts.
///
/// When a request is matched, these are all merged and fed into the chain of combinators to
/// be transformed before being passed into an eventual handler.
///
/// Combinators may move arbitrary subsets of the context's request scoped state, and return
/// arbitrary sets of state to merge for later combinators to use. In this way, the data
/// dependencies between middlewares / handlers can be expressed at compile time, without
/// introducing unnecessary coupling between components that are logically unrelated.
///
/// ```
/// use hyper::Body;
/// use hyperbole::{hlist, App, Hlist};
///
/// #[derive(Copy, Clone)]
/// struct DbHandle;
///
/// struct A;
/// struct B;
///
/// let _ctx = App::new()
///     .context()
///     .inject(DbHandle)
///     // move nothing, and return nothing to be merged
///     .map(|cx: Hlist![]| cx)
///     // move req body, but merge it back
///     .map(|cx: Hlist![Body]| cx)
///     // move req body, and merge an A and B
///     .map(|cx: Hlist![Body]| hlist![A, B])
///     // subset ordering doesn't matter
///     .map(|cx: Hlist![B, DbHandle, A]| cx)
///     .then(|cx: Hlist![A]| async { cx })
///     .map(|cx: Hlist![A, B]| cx)
///     .then(|cx: Hlist![B]| async { cx });
/// ```
///
/// At any point in a context chain, a handler can be registered by calling [handle] or one
/// of its analogues (ex: [get], [post]). Like middleware combinators, handlers move a subset
/// of the request scoped state into themselves, but instead of returning more state to merge
/// they return a value that implements [Reply].
///
/// ```
/// use hyper::Body;
/// use hyperbole::{access, path, record, record_args, App, Hlist};
///
/// let _ctx = App::new()
///     .context_path(path![dynamic: u32])
///     // GET /:dynamic/echo_req
///     .get(path!["echo_req"], |cx: Hlist![Body]| async move {
///         // hlists can be converted into tuples
///         let (body,) = cx.into();
///         format!("echo: {:?}", body)
///     })
///     // GET /:dynamic/tell_dynamic
///     .get(path!["tell_dynamic"], |cx: record![dynamic]| async move {
///         // or use the access! macro for named field accesses
///         format!("dynamic is {}", access!(&cx.dynamic))
///     })
///     .path(path!["all" / "the" / "subpaths"])
///     // GET /:dynamic/all/the/subpaths/discrete
///     .get(path!["discrete"], fn_handler);
///
/// // or use the record_args attribute to reduce boilerplate
/// #[record_args]
/// async fn fn_handler(dynamic: u32, _body: Body) -> &'static [u8] {
///     println!("dynamic: {}", dynamic);
///     println!("reqbody: {:?}", _body);
///
///     b"here's an octet-stream"
/// }
/// ```
///
/// # Error Handling
/// Errors that arise during request resolution are represented in the context as [coproducts]
/// (a generalization of enums). When a fallible middleware is used ([try_map] or [try_then]),
/// an additional error variant is added to the context's error coproduct. This also applies
/// to parse errors of dynamic path parameters (which are wrapped in a [tree::UriError]).
///
/// If a fallible middleware returns `Err`, the request being processed short circuits and cannot
/// be recovered. The specific error response returned to the client can however be modified by
/// [map_errs] or [map_err]. The former transforms the complete error coproduct, while the latter
/// maps over a single variant.
///
/// Much like with request scoped state, any referenced errors in a [map_errs] or [map_err] must
/// appear in some fallible combinator. This is enforced at compile time.
///
/// ```
/// use hyper::StatusCode;
/// use hyperbole::{
///     body::{jsonr, JsonBodyError},
///     record,
///     reply::Reply,
///     App, Coprod,
/// };
///
/// let _app = App::new()
///     .context()
///     // attempt to parse the body as a json object:
///     .try_then(jsonr::<record![x: u32, y: String]>)
///     // if the above fails, we can adjust the error with map_err:
///     .map_err(|err: JsonBodyError| err)
///     // or we can adjust all possible errors with map_errs:
///     .map_errs(|errs| {
///         let code = StatusCode::INTERNAL_SERVER_ERROR;
///         let err = format!("{:?}", errs).with_status(code);
///
///         // return type must be a coproduct as well
///         <Coprod![_]>::inject(err)
///     })
///     .collapse();
/// ```
///
/// # Limitations
/// Due to the extensive use of type inference to extract subsets of the request scoped state,
/// the state may not contain duplicate instances of a type. That is, it is a *set*, and not
/// a *list*. This property arises without explicit enforcement; type inference will simply
/// begin failing if duplicate types are encountered.
///
/// ```compile_fail,E0282
/// use hyperbole::{hlist, App, Hlist};
///
/// struct A(u32);
///
/// let _app = App::new()
///     .context()
///     // merge an A
///     .map(|cx: Hlist![]| hlist![A(1)])
///     // merge an A (state now contains two `A`s)
///     .map(|cx: Hlist![]| hlist![A(2)])
///     // this fails during type inference, because it's ambiguous _which_ A we want
///     //
///     // error[E0282]: type annotations needed
///     //     cannot infer type for type parameter `TailIndex`
///     .map(|cx: Hlist![A]| cx)
///     .collapse();
/// ```
///
/// [Named fields][field::Field] can be used to disambiguate between what would otherwise be
/// duplicate types. [path!] in particular takes advantage of this to allow multiple instances
/// of common primitive types like `u32` or `String` to be extracted from a uri.
///
/// The above example can be rewritten using named fields to avoid the inference failure:
///
/// ```
/// use hyperbole::{record, App};
///
/// struct A(u32);
///
/// let _app = App::new()
///     .context()
///     .map(|cx: record![]| record![first = A(1)])
///     .map(|cx: record![]| record![second = A(2)])
///     // we want the A called 'second'
///     .map(|cx: record![second]| cx)
///     // we want the A called 'first'
///     .map(|cx: record![first]| cx)
///     // we want both of them
///     .map(|cx: record![first, second]| cx)
///     .collapse();
/// ```
///
/// [handle]: Ctx::handle
/// [get]: Ctx::get
/// [post]: Ctx::post
/// [coproducts]: coproduct
/// [try_map]: Ctx::try_map
/// [try_then]: Ctx::try_then
/// [map_errs]: Ctx::map_errs
/// [map_err]: Ctx::map_err
pub struct Ctx<P, L> {
    app: App,
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

impl<P: 'static, L: Sync + Send + Clone + 'static> Ctx<P, L> {
    fn link_next<Ln, F: FnOnce(L) -> Ln>(self, wrap: F) -> Ctx<P, Ln> {
        Ctx {
            app: self.app,
            chain: self.chain.link_next(wrap),
        }
    }

    /// Inject a cloneable value into the request scoped state.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{f, hlist, record, App, Hlist};
    ///
    /// let _ctx = App::new()
    ///     .context()
    ///     .inject("just an &str")
    ///     .map(|cx: Hlist![&str]| hlist![])
    ///     .inject(f![xyz = "this is a named field"])
    ///     .map(|cx: record![xyz]| hlist![]);
    /// ```
    pub fn inject<T: Clone>(self, value: T) -> Ctx<P, Inject<L, T>>
    where Inject<L, T>: Link<Init, P> {
        self.link_next(|link| Inject::new(link, value))
    }

    /// Inject an hlist of cloneable values into the request scoped state.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{record, App};
    ///
    /// let _ctx = App::new()
    ///     .context()
    ///     .inject_all(record![a = "asdf", b = 42])
    ///     .map(|cx: record![b, a]| cx)
    ///     .inject_all(record![c = ()])
    ///     .map(|cx: record![a, b, c]| cx);
    /// ```
    pub fn inject_all<T: Clone>(self, values: T) -> Ctx<P, InjectAll<L, T>>
    where InjectAll<L, T>: Link<Init, P> {
        self.link_next(|link| InjectAll::new(link, values))
    }

    /// Transform a subset of the request scoped state with a closure.
    ///
    /// The provided closure should accept an hlist argument, and return an hlist.
    ///
    /// The argument hlist may consist of any subset of types that are present within the
    /// context's state up to this point. Each element will be removed from the context's
    /// state and *moved* into `f` upon execution (making them inaccessible to subsequent
    /// middlewares and handlers).
    ///
    /// Likewise, any types in the returned hlist will be *moved* into the context's state.
    ///
    /// # Examples
    /// ```
    /// use hyper::Body;
    /// use hyperbole::{hlist, record_args, App, Hlist};
    ///
    /// #[record_args]
    /// fn fun(_: Body, _: u32) -> Hlist![] {
    ///     hlist![]
    /// }
    ///
    /// let _ctx = App::new()
    ///     .context()
    ///     .map(|cx: Hlist![Body]| cx)
    ///     .map(|cx: Hlist![]| hlist![12345])
    ///     .map(fun);
    /// ```
    pub fn map<F, Args, Ix, Merge>(self, f: F) -> Ctx<P, Map<L, F, Args, Ix>>
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
    /// The argument hlist may consist of any subset of types that are present within the
    /// context's state up to this point. Each element will be removed from the context's
    /// state and *moved* into `f` upon execution (making them inaccessible to subsequent
    /// middlewares and handlers).
    ///
    /// If the closure returns `Ok`, any types in the returned hlist will be *moved* into the
    /// context's state.
    ///
    /// If the closure returns `Err`, the request will short circuit with a response created
    /// via the error's [Reply] implementation.
    ///
    /// For subsequent combinators, the context's error type will contain an additional variant
    /// for `E`.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{access, path, record, App};
    ///
    /// let _ctx = App::new()
    ///     .context_path(path![a: u32 / b: u32])
    ///     .try_map(|cx: record![a, b]| match access!(&cx.a) > access!(&cx.b) {
    ///         false => Err("uh oh"),
    ///         true => Ok(cx),
    ///     })
    ///     .map_err(|e: &str| "e is the above error, if it happened");
    /// ```
    pub fn try_map<F, Args, Ix, Merge, E>(self, f: F) -> Ctx<P, TryMap<L, F, Args, Ix>>
    where
        F: Fn(Args) -> Result<Merge, E>,
        Merge: HList,
        E: Reply,
        TryMap<L, F, Args, Ix>: Link<Init, P>,
    {
        self.link_next(|link| TryMap::new(link, f))
    }

    /// Transform a subset of the request scoped state with a closure that returns a
    /// future.
    ///
    /// The provided closure should accept an hlist argument, and return a future that
    /// evaluates to an hlist.
    ///
    /// The argument hlist may consist of any subset of types that are present within the
    /// context's state up to this point. Each element will be removed from the context's
    /// state and *moved* into `f` upon execution (making them inaccessible to subsequent
    /// middlewares and handlers).
    ///
    /// Likewise, any types in the returned hlist will be *moved* into the context's state.
    ///
    /// # Examples
    /// ```
    /// use hyper::Body;
    /// use hyperbole::{hlist, record_args, App, Hlist};
    ///
    /// #[record_args]
    /// async fn fun(_: Body) -> Hlist![] {
    ///     hlist![]
    /// }
    ///
    /// let _ctx = App::new()
    ///     .context()
    ///     .then(|cx: Hlist![Body]| async move { cx })
    ///     .then(|cx: Hlist![]| async move { cx })
    ///     .then(fun);
    /// ```
    pub fn then<F, Args, Ix, Fut, Merge>(self, f: F) -> Ctx<P, Then<L, F, Args, Ix>>
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
    /// The provided closure should accept an hlist argument, and return a future that evaluates
    /// to an hlist in a [Result] (where the error type implements [Reply]).
    ///
    /// The argument hlist may consist of any subset of types that are present within the
    /// context's state up to this point. Each element will be removed from the context's
    /// state and *moved* into `f` upon execution (making them inaccessible to subsequent
    /// middlewares and handlers).
    ///
    /// If the future evaluates to `Ok`, any types in the returned hlist will be *moved* into
    /// the context's state.
    ///
    /// If the future evaluates to `Err`, the request will short circuit with a response created
    /// via the error's [Reply] implementation.
    ///
    /// For subsequent combinators, the context's error type will contain an additional variant
    /// for `E`.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{path, record, App};
    ///
    /// let _ctx = App::new()
    ///     .context_path(path![a: f64 / b: String])
    ///     .try_then(|cx: record![a, b]| async move {
    ///         let (a, b) = cx.into();
    ///         if *a == 3.14159265 && *b != "blue" {
    ///             Err("always blue!")
    ///         } else {
    ///             Ok(record![color = "it was blue!"])
    ///         }
    ///     })
    ///     .map(|cx: record![color]| cx);
    /// ```
    pub fn try_then<F, Args, Ix, Fut, Merge, E>(self, f: F) -> Ctx<P, TryThen<L, F, Args, Ix>>
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
    /// Any [Coproduct] may be returned, so long as any variants it contains all implement
    /// [Reply].
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{record, App, Coprod};
    ///
    /// let _ctx = App::new()
    ///     .context()
    ///     // without any fallible combinators, the error is an uninhabitable enum:
    ///     .map_errs(|err: Coprod![]| -> Coprod![] { match err {} })
    ///     .map(|cx: record![]| cx)
    ///     .collapse();
    /// ```
    pub fn map_errs<F, E>(self, f: F) -> Ctx<P, MapErrs<L, F>>
    where
        F: Fn(<L as Link<Init, P>>::Error) -> E,
        E: IsCoproduct + Reply,
        L: Link<Init, P>,
        MapErrs<L, F>: Link<Init, P>,
    {
        self.link_next(|link| MapErrs::new(link, f))
    }

    /// Transform a single variant of the context's error type with a closure.
    ///
    /// This can be used to selectively modify only a single type of error. Note that if more
    /// than one instance of the same error type may have occurred, this will only affect the
    /// most recent of them.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{record, record_args, App};
    ///
    /// fn fallible_a(_: record![]) -> Result<record![], String> {
    ///     Err("uh oh".to_owned())
    /// }
    ///
    /// #[record_args]
    /// fn fallible_b() -> Result<record![], Vec<u8>> {
    ///     Err(b"uh oh".to_vec())
    /// }
    ///
    /// let _app = App::new()
    ///     .context()
    ///     .try_map(fallible_a)
    ///     .try_map(fallible_b)
    ///     .map_err(|e: String| "it was String")
    ///     .map_err(|e: Vec<u8>| "it was Vec<u8>")
    ///     .collapse();
    /// ```
    pub fn map_err<F, E, Ix, R>(self, f: F) -> Ctx<P, MapErr<L, F, E, Ix>>
    where
        F: Fn(E) -> R,
        R: Reply,
        MapErr<L, F, E, Ix>: Link<Init, P>,
    {
        self.link_next(|link| MapErr::new(link, f))
    }

    /// Append additional path segments to this context's base path. Any new parameters parsed
    /// from the uri will be merged into the context's state at this point.
    ///
    /// The [path!] macro can be used to construct an appropriate [`PathSpec`].
    ///
    /// When a request is being handled, the concatenated path specification is parsed before
    /// any middlewares execute. However, all extracted parameters (and parsing errors) are
    /// deferred such that they only appear at the point where they were specified.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{path, record, tree::UriError, App};
    /// use std::num::ParseFloatError;
    ///
    /// let _ctx = App::new()
    ///     .context()
    ///     .path(path!["first" / x: usize / y: f64])
    ///     .map(|cx: record![x]| cx)
    ///     .map_err(|e: UriError<ParseFloatError>| e.item)
    ///     .map(|cx: record![y]| cx)
    ///     .map(|cx: record![x, y]| cx)
    ///     // GET /first/:x/:y/abc
    ///     .get(path!["abc"], |cx: record![x, y]| async { "" });
    /// ```
    pub fn path<_P, Ix>(self, spec: PathSpec<_P>) -> Ctx<Add2<P, Params<_P>>, Path<L, _P, Ix>>
    where
        P: Add<Params<_P>>,
        _P: Parser<Segment>,
        Path<L, _P, Ix>: Link<Init, Add2<P, Params<_P>>>,
    {
        Ctx {
            app: self.app,
            chain: self.chain.add_path(spec).link_next(Path::new),
        }
    }

    /// Register a request handler for this context's base path with `spec` appended to it.
    ///
    /// The provided `handler` closure should accept an hlist argument, and return a future
    /// that evaluates to an http response (via the [Reply] trait).
    ///
    /// The argument hlist may consist of any subset of types that are present within the
    /// context's state up to this point, or any parameters parsed from the provided path
    /// `spec`.
    ///
    /// If an incoming request matches this route, every middleware accumulated in the context
    /// up to this point will execute. Assuming none of them short circuit with an error, this
    /// handler will then be executed.
    ///
    /// # Examples
    /// ```
    /// use hyper::Body;
    /// use hyperbole::{hlist, path, record, record_args, reply::Reply, App, Hlist};
    ///
    /// #[record_args]
    /// async fn doit(baz: f64) -> &'static str {
    ///     "&'static str implements Reply"
    /// }
    ///
    /// async fn more(cx: Hlist![Body, u32]) -> &'static [u8] {
    ///     b"so does &'static [u8]"
    /// }
    ///
    /// async fn using_impl(cx: Hlist![]) -> impl Reply {
    ///     vec![1, 2, 3, 4, 5]
    /// }
    ///
    /// let _ctx = App::new()
    ///     .context_path(path!["foo" / "bar" / baz: f64])
    ///     .get(path!["doit"], doit)
    ///     .map(|cx: record![baz]| hlist![15])
    ///     .get(path!["more" / neat: u32], more)
    ///     .get(path!["more"], more)
    ///     .get(path!["more" / neat: u32 / "nested"], more)
    ///     .get(path!["impl_reply"], using_impl);
    /// ```
    ///
    /// # Panics
    /// This method will panic if the complete path conflicts with any other route registered
    /// under the same http method.
    ///
    /// ```should_panic
    /// use hyperbole::{path, record, App};
    ///
    /// // 'a handler is already registered for path "/conflict"'
    /// let _ctx = App::new()
    ///     .context()
    ///     .get(path!["conflict"], |_: record![]| async { "" })
    ///     .get(path!["conflict"], |_: record![]| async { "" });
    /// ```
    ///
    /// ```should_panic
    /// use hyperbole::{path, record, App};
    ///
    /// // 'wildcard ":param" conflicts with existing children in path "/:param"'
    /// let _ctx = App::new()
    ///     .context()
    ///     .get(path!["something"], |_: record![]| async { "" })
    ///     .get(path![param: u32], |_: record![]| async { "" });
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

        let path = format!("{}", chain.path());

        self.app.get_node_mut(method).insert(&path, Box::new(chain));

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
    /// argument, which should be a closure that could be passed to [try_then]. It will behave
    /// as if added between the path combinator and handler (that is, it has access to any new
    /// types introduced in `spec`, and merges types accessible to `handler`).
    ///
    /// This is useful for specifying a different request body parser for multiple handlers
    /// that otherwise share the same chain of middlewares.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{body::jsonr, path, record, App};
    ///
    /// async fn handle_abc(cx: record![a: u32, b: String, c: f64]) -> &'static str {
    ///     "neat"
    /// }
    ///
    /// let _app = App::new()
    ///     .context()
    ///     .get_with(path![a: u32], jsonr::<record![b, c]>, handle_abc)
    ///     .collapse();
    /// ```
    ///
    /// # Panics
    /// This method will panic if the complete path conflicts with any other route registered
    /// under the same http method.
    ///
    /// ```should_panic
    /// use hyperbole::{path, record, App};
    /// use std::convert::Infallible;
    ///
    /// async fn noop(cx: record![]) -> Result<record![], Infallible> {
    ///     Ok(cx)
    /// }
    ///
    /// // 'a handler is already registered for path "/conflict"'
    /// let _ctx = App::new()
    ///     .context()
    ///     .get_with(path!["conflict"], noop, |_: record![]| async { "" })
    ///     .get_with(path!["conflict"], noop, |_: record![]| async { "" });
    /// ```
    ///
    /// ```should_panic
    /// use hyperbole::{path, record, App};
    /// use std::convert::Infallible;
    ///
    /// async fn noop(cx: record![]) -> Result<record![], Infallible> {
    ///     Ok(cx)
    /// }
    ///
    /// // 'wildcard ":param" conflicts with existing children in path "/:param"'
    /// let _ctx = App::new()
    ///     .context()
    ///     .get_with(path!["something"], noop, |_: record![]| async { "" })
    ///     .get_with(path![param: u32], noop, |_: record![]| async { "" });
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

        let path = format!("{}", chain.path());

        self.app.get_node_mut(method).insert(&path, Box::new(chain));

        self
    }

    handle_with!(
        [get_with, Method::GET],
        [post_with, Method::POST],
        [put_with, Method::PUT],
        [patch_with, Method::PATCH],
        [delete_with, Method::DELETE]
    );

    /// Collapse this context and return to the base [App].
    ///
    /// This discards any accumulated combinators and path specifications, while retaining
    /// handlers registered via [handle] (or helpers like [get], [post], etc).
    ///
    /// [handle]: Ctx::handle
    /// [get]: Ctx::get
    /// [post]: Ctx::post
    pub fn collapse(self) -> App {
        self.app
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

mod sealed {
    pub trait Seal {}
}

/// Types that represent coproducts.
pub trait IsCoproduct: sealed::Seal {}

impl sealed::Seal for CNil {}
impl IsCoproduct for CNil {}

impl<H, T: sealed::Seal> sealed::Seal for Coproduct<H, T> {}
impl<H, T: IsCoproduct> IsCoproduct for Coproduct<H, T> {}
