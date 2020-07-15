//! Middleware combinators.
use super::{field::Field, r, reply::Reply, Response, R};
use headers::{Cookie, Header, HeaderMapExt};
use http::{header::HeaderName, HeaderMap, HeaderValue};
use hyper::StatusCode;
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
/// use hyperbole::{mw, Ctx, R};
///
/// let _ctx = Ctx::default()
///     .try_map(mw::header(ACCEPT))
///     .map(|cx: R![HeaderValue]| cx);
/// ```
pub fn header(
    name: HeaderName,
) -> impl Fn(R![HeaderMap]) -> Result<R![HeaderValue, HeaderMap], HeaderError> {
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
/// use hyperbole::{mw, Ctx, R};
///
/// let _ctx = Ctx::default()
///     .map(mw::header_opt(ACCEPT))
///     .map(|cx: R![Option<HeaderValue>]| cx);
/// ```
pub fn header_opt(
    name: HeaderName,
) -> impl Fn(R![HeaderMap]) -> R![Option<HeaderValue>, HeaderMap] {
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
/// use hyperbole::{mw, Ctx, R};
///
/// let _ctx = Ctx::default()
///     .try_map(mw::typed_header::<Authorization<Basic>>)
///     .map(|cx: R![Authorization<Basic>]| {
///         let user = cx.head.0.username();
///         let pass = cx.head.0.password();
///         cx
///     });
/// ```
pub fn typed_header<H: Header>(cx: R![HeaderMap]) -> Result<R![H, HeaderMap], HeaderError> {
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
/// use hyperbole::{mw, Ctx, R};
///
/// let _ctx = Ctx::default().map(mw::typed_header_opt::<ContentType>).map(
///     |cx: R![Option<ContentType>]| match cx.get() {
///         Some(ctype) => cx,
///         None => cx,
///     },
/// );
/// ```
pub fn typed_header_opt<H: Header>(cx: R![HeaderMap]) -> R![Option<H>, HeaderMap] {
    let h = cx.head.typed_get();
    cx.prepend(h)
}

/// An error encountered during cookie resolution.
#[derive(Clone, Debug, Error)]
pub enum CookieError {
    /// The cookie header itself is missing.
    #[error("missing Cookie header")]
    MissingHeader,

    /// The requested cookie is missing.
    #[error("missing cookie {:?}", .0)]
    MissingCookie(&'static str),
}

impl Reply for CookieError {
    #[inline]
    fn into_response(self) -> Response {
        hyper::Response::builder()
            .status(StatusCode::BAD_REQUEST)
            .body(format!("{}", self).into())
            .unwrap()
    }
}

/// Extract a cookie from the request context. The cookie name should be passed via const generic
/// parameter.
///
/// The extracted cookie will be injected into the context as a named field.
///
/// Use with [`Ctx::try_map`][super::Ctx::try_map].
///
/// # Examples
/// ```
/// use hyperbole::{mw, Ctx, R};
///
/// let _ctx = Ctx::default()
///     .try_map(mw::cookie::<"foobar">)
///     .map(|cx: R![foobar: String]| {
///         println!("cookie value is {:?}", cx.head);
///         cx
///     });
/// ```
pub fn cookie<const NAME: &'static str>(
    cx: R![HeaderMap],
) -> Result<R![Field<String, NAME>, HeaderMap], CookieError> {
    let cookie = (cx.head)
        .typed_get::<Cookie>()
        .ok_or(CookieError::MissingHeader)?;

    match cookie.get(NAME).map(|v| v.to_owned()) {
        Some(val) => Ok(cx.prepend(val.into())),
        None => Err(CookieError::MissingCookie(NAME)),
    }
}

/// Extract an optional cookie from the request context. The cookie name should be passed via const
/// generic parameter.
///
/// The extracted cookie will be injected into the context as a named field.
///
/// Use with [`Ctx::map`][super::Ctx::map].
///
/// # Examples
/// ```
/// use hyperbole::{mw, Ctx, R};
///
/// let _ctx = Ctx::default().map(mw::cookie_opt::<"some_cookie">).map(
///     |cx: R![some_cookie: Option<String>]| {
///         println!("cookie value is {:?}", cx.head);
///         cx
///     },
/// );
/// ```
pub fn cookie_opt<const NAME: &'static str>(
    cx: R![HeaderMap],
) -> R![Field<Option<String>, NAME>, HeaderMap] {
    let cookie = (cx.head)
        .typed_get::<Cookie>()
        .and_then(|c| c.get(NAME).map(|v| v.to_owned()));

    cx.prepend(cookie.into())
}

/// Rename a named field in the request scoped state.
///
/// Use with [`Ctx::map`][super::Ctx::map].
///
/// # Examples
/// ```
/// use hyperbole::{mw, r, Ctx, R};
///
/// let _ctx = Ctx::with_state(r![foo = "hello world"])
///     .map(|cx: R![foo: _]| cx)
///     .map(mw::rename::<_, "foo", "bar">)
///     .map(|cx: R![bar: _]| cx);
/// ```
pub fn rename<T, const OLD: &'static str, const NEW: &'static str>(
    cx: R![Field<T, OLD>],
) -> R![
       Field<T, NEW>
   ] {
    r![cx.head.into_inner().into()]
}
