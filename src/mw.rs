//! Middleware combinators.
use super::{reply::Reply, Response};
use frunk_core::Hlist;
use headers::{Header, HeaderMapExt};
use http::{header::HeaderName, HeaderMap, HeaderValue};
use hyper::StatusCode;

/// An error encountered during header resolution.
#[derive(Clone, Debug)]
pub struct HeaderError(HeaderName);

impl Reply for HeaderError {
    #[inline]
    fn into_response(self) -> Response {
        let err = format!("header {:?} missing or malformed", self.0);

        hyper::Response::builder()
            .status(StatusCode::BAD_REQUEST)
            .body(err.into())
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
