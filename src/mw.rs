//! Middleware combinators.
use super::{f, reply::Reply, Response};
use frunk_core::Hlist;
use headers::{Header, HeaderMapExt};
use http::{header::HeaderName, HeaderMap, HeaderValue, Method, Uri};
use hyper::StatusCode;
use hyper_staticfile::{resolve_path, ResponseBuilder};
use std::{convert::TryFrom, future::Future, io, path::PathBuf};
use thiserror::Error;

/// An error encountered during header resolution.
#[derive(Clone, Debug, Error)]
#[error("header {:?} missing or malformed", .0)]
pub struct HeaderError(HeaderName);

impl Reply for HeaderError {
    #[inline]
    fn into_response(self) -> Response {
        hyper::Response::builder()
            .status(StatusCode::BAD_REQUEST)
            .body(format!("{}", self).into())
            .unwrap()
    }
}

/// Extract a [HeaderValue] from the request context by name.
///
/// This is generally less useful than [typed_header] because only a single [HeaderValue] can
/// exist in a context at a time.
///
/// Use with [`Ctx::try_map`][super::Ctx::try_map].
///
/// # Examples
/// ```
/// use hyper::header::{HeaderValue, ACCEPT};
/// use hyperbole::{mw, App, Hlist};
///
/// let _app = App::empty()
///     .context()
///     .try_map(mw::header(ACCEPT))
///     .map(|cx: Hlist![HeaderValue]| cx)
///     .collapse();
/// ```
pub fn header(
    name: HeaderName,
) -> impl Fn(Hlist![HeaderMap]) -> Result<Hlist![HeaderValue, HeaderMap], HeaderError> {
    move |cx| match cx.head.get(&name).cloned() {
        Some(h) => Ok(cx.prepend(h)),
        None => Err(HeaderError(name.clone())),
    }
}

/// Extract an optional [HeaderValue] from the request context by name.
///
/// This is generally less useful than [typed_header_opt] because only a single [Option<HeaderValue>]
/// can exist in a context at a time.
///
/// Use with [`Ctx::map`][super::Ctx::map].
///
/// # Examples
/// ```
/// use hyper::header::{HeaderValue, ACCEPT};
/// use hyperbole::{mw, App, Hlist};
///
/// let _app = App::empty()
///     .context()
///     .map(mw::header_opt(ACCEPT))
///     .map(|cx: Hlist![Option<HeaderValue>]| cx)
///     .collapse();
/// ```
pub fn header_opt(
    name: HeaderName,
) -> impl Fn(Hlist![HeaderMap]) -> Hlist![Option<HeaderValue>, HeaderMap] {
    move |cx| {
        let h = cx.head.get(&name).cloned();
        cx.prepend(h)
    }
}

/// Extract a typed header from the request context.
///
/// Use with [`Ctx::try_map`][super::Ctx::try_map].
///
/// # Examples
/// ```
/// use headers::{authorization::Basic, Authorization};
/// use hyperbole::{mw, App, Hlist};
///
/// let _app = App::empty()
///     .context()
///     .try_map(mw::typed_header::<Authorization<Basic>>)
///     .map(|cx: Hlist![Authorization<Basic>]| {
///         let user = cx.head.0.username();
///         let pass = cx.head.0.password();
///         cx
///     })
///     .collapse();
/// ```
pub fn typed_header<H: Header>(cx: Hlist![HeaderMap]) -> Result<Hlist![H, HeaderMap], HeaderError> {
    match cx.head.typed_get() {
        Some(h) => Ok(cx.prepend(h)),
        None => Err(HeaderError(H::name().clone())),
    }
}

/// Extract an optional typed header from the request context.
///
/// Use with [`Ctx::map`][super::Ctx::map].
///
/// # Examples
/// ```
/// use headers::ContentType;
/// use hyperbole::{mw, App, Hlist};
///
/// let _app = App::empty()
///     .context()
///     .map(mw::typed_header_opt::<ContentType>)
///     .map(|cx: Hlist![Option<ContentType>]| match cx.get() {
///         Some(ctype) => cx,
///         None => cx,
///     })
///     .collapse();
/// ```
pub fn typed_header_opt<H: Header>(cx: Hlist![HeaderMap]) -> Hlist![Option<H>, HeaderMap] {
    let h = cx.head.typed_get();
    cx.prepend(h)
}

/// Handle a request by extracting a [Reply] from the request context.
///
/// This can be used to terminate a middleware chain if handling a request doesn't require
/// any extra logic.
///
/// # Examples
/// ```
/// use hyperbole::{f, hlist, mw, path, record, App, Hlist};
///
/// let _app = App::empty()
///     .context()
///     .map(|_: Hlist![]| hlist!["this is my response"])
///     .get(path!["i-want-my-str"], mw::extract::<&str>)
///     .map(|_: Hlist![]| record![foo = "here is fresh foo"])
///     .get(path!["unhand-me-a-foo"], mw::extract::<f![foo]>)
///     .collapse();
/// ```
pub async fn extract<T: Reply>(cx: Hlist![T]) -> T {
    cx.head
}

/// A filesystem error.
#[derive(Debug, Error)]
pub enum FsError {
    /// An IO error.
    #[error("io error: {}", .0)]
    Io(#[from] io::Error),

    /// An HTTP error.
    #[error("http error: {}", .0)]
    Http(#[from] http::Error),
}

impl Reply for FsError {
    #[inline]
    fn into_response(self) -> Response {
        hyper::Response::builder()
            .status(StatusCode::INTERNAL_SERVER_ERROR)
            .body("internal server error".into())
            .unwrap()
    }
}

/// Handle a request by serving a file from the filesystem. The file to be served will be the
/// request uri path appended to `base_path`.
///
/// # Examples
/// ```
/// use hyperbole::{mw, path, App};
///
/// let _app = App::empty()
///     .not_found(mw::filesystem("/srv"))
///     .context()
///     .get(path!["a" / "whatever.jpg"], mw::filesystem("/srv"))
///     .get(path!["b" / *extra: String], mw::filesystem("/opt"))
///     .collapse();
/// ```
pub fn filesystem(base_path: &str) -> impl Fn(Hlist![Method, Uri, HeaderMap]) -> FsFuture {
    let root = PathBuf::from(base_path);

    move |cx| fs_inner(root.clone(), cx.head, Ok(cx.tail.head), cx.tail.tail.head)
}

/// Handle a request by serving a file from the filesystem. Unlike [filesystem], this will not
/// serve the complete request uri, but the named field `path: String`.
///
/// The file to be served will be the value of `path` appended to `base_path`.
///
/// # Examples
/// ```
/// use hyperbole::{mw, path, App};
///
/// let _app = App::empty()
///     .context()
///     .get(path!["files" / *path: String], mw::filesystem_path("/srv"))
///     .collapse();
/// ```
pub fn filesystem_path(
    base_path: &str,
) -> impl Fn(Hlist![Method, f![path: String], HeaderMap]) -> FsFuture {
    let root = PathBuf::from(base_path);

    move |cx| {
        let uri = Uri::try_from(cx.tail.head.into_inner()).map_err(|e| e.into());
        fs_inner(root.clone(), cx.head, uri, cx.tail.tail.head)
    }
}

/// The opaque future returned by [filesystem] and [filesystem_path].
pub type FsFuture = impl Future<Output = Result<Response, FsError>>;

type UriRes = http::Result<Uri>;

async fn fs_inner(path: PathBuf, m: Method, u: UriRes, h: HeaderMap) -> Result<Response, FsError> {
    let uri = u?;

    ResponseBuilder::new()
        .request_parts(&m, &uri, &h)
        .build(resolve_path(path, uri.path()).await?)
        .map_err(|e| e.into())
}
