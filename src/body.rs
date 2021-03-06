//! Helpers for parsing request bodies.
use super::{field::IsoDecode, r, reply::Reply, Response, R};
use bytes::{buf::BufExt, Buf, Bytes};
use frunk_core::hlist::{HCons, HList};
use futures::future::FutureExt;
use headers::{ContentType, HeaderMapExt};
use http::HeaderMap;
use hyper::{body, Body, StatusCode};
use mime::Mime;
use serde::de::DeserializeOwned;
use std::future::Future;
use thiserror::Error;

macro_rules! bad_request_display {
    ($t: ty) => {
        impl Reply for $t {
            #[inline]
            fn into_response(self) -> Response {
                hyper::Response::builder()
                    .status(StatusCode::BAD_REQUEST)
                    .body(format!("{}", self).into())
                    .unwrap()
            }
        }
    };
}

/// An error encountered during json deserialization of a request body.
#[derive(Debug, Error)]
pub enum JsonBodyError {
    /// Error occurred while reading the request body.
    #[error("failed to read body: {}", .0)]
    Body(#[from] hyper::Error),

    /// Error occurred during deserialization.
    #[error("failed to parse body: {}", .0)]
    Json(#[from] serde_json::Error),
}

bad_request_display! { JsonBodyError }

/// Deserialize a value from a json request body.
///
/// Use with [`Ctx::handle_with`][super::Ctx::handle_with] or [`Ctx::try_then`][super::Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::json, record_args, uri, Ctx};
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct ThingRequest {
///     x: u32,
///     y: String,
/// }
///
/// #[record_args]
/// async fn the_thing(_: ThingRequest) -> &'static str {
///     "yepperz"
/// }
///
/// let _ctx = Ctx::default()
///     // inline with get_with:
///     .get_with(uri!["the-thing"], json::<ThingRequest>, the_thing)
///     // or as a middleware:
///     .try_then(json::<ThingRequest>)
///     .get(uri!["the-thing" / "via-mw"], the_thing);
/// ```
pub async fn json<T: DeserializeOwned>(cx: R![Body]) -> Result<R![T], JsonBodyError> {
    let bodyr = body::aggregate(cx.head).await?.reader();

    serde_json::from_reader(bodyr)
        .map_err(JsonBodyError::Json)
        .map(|t| r![t])
}

/// Deserialize an anonymous record from a json request body.
///
/// This can be used to specify a request body without declaring a bespoke request struct,
/// while maintaining type safe access to the payload.
///
/// Any fields of the record will be merged into the context's state as if they were provided
/// inline.
///
/// Use with [`Ctx::handle_with`][super::Ctx::handle_with] or [`Ctx::try_then`][super::Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::jsonr, record_args, uri, Ctx, R};
///
/// #[record_args]
/// async fn the_thing(x: u32, y: String, z: f64) -> &'static str {
///     "yepperz"
/// }
///
/// let _ctx = Ctx::default()
///     // inline with get_with:
///     .get_with(uri!["the-thing"], jsonr::<R![x: _, y: _, z: _]>, the_thing)
///     // or as a middleware:
///     .try_then(jsonr::<R![x: _, y: _]>)
///     .get(uri!["the-thing" / z: f64], the_thing);
/// ```
pub async fn jsonr<T: IsoDecode>(cx: R![Body]) -> Result<T, JsonBodyError> {
    let bodyr = body::aggregate(cx.head).await?.reader();

    serde_json::from_reader(bodyr)
        .map_err(JsonBodyError::Json)
        .map(T::from_repr)
}

/// An error encountered during form deserialization of a request body.
#[derive(Debug, Error)]
pub enum FormBodyError {
    /// Error occurred while reading the request body.
    #[error("failed to read body: {}", .0)]
    Body(#[from] hyper::Error),

    /// Error occurred during deserialization.
    #[error("failed to parse body: {}", .0)]
    Form(#[from] serde_urlencoded::de::Error),
}

bad_request_display! { FormBodyError }

/// Deserialize a value from an `x-www-form-urlencoded` request body.
///
/// Use with [`Ctx::handle_with`][super::Ctx::handle_with] or [`Ctx::try_then`][super::Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::form, record_args, uri, Ctx};
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct ThingRequest {
///     x: u32,
///     y: String,
/// }
///
/// #[record_args]
/// async fn the_thing(_: ThingRequest) -> &'static str {
///     "yepperz"
/// }
///
/// let _ctx = Ctx::default()
///     // inline with get_with:
///     .get_with(uri!["the-thing"], form::<ThingRequest>, the_thing)
///     // or as a middleware:
///     .try_then(form::<ThingRequest>)
///     .get(uri!["the-thing" / "via-mw"], the_thing);
/// ```
pub async fn form<T: DeserializeOwned>(cx: R![Body]) -> Result<R![T], FormBodyError> {
    let bodyr = body::aggregate(cx.head).await?.reader();

    serde_urlencoded::from_reader(bodyr)
        .map_err(FormBodyError::Form)
        .map(|t| r![t])
}

/// Deserialize an anonymous record from an `x-www-form-urlencoded` request body.
///
/// This can be used to specify a request body without declaring a bespoke request struct,
/// while maintaining type safe access to the payload.
///
/// Any fields of the record will be merged into the context's state as if they were provided
/// inline.
///
/// Use with [`Ctx::handle_with`][super::Ctx::handle_with] or [`Ctx::try_then`][super::Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::formr, record_args, uri, Ctx, R};
///
/// #[record_args]
/// async fn the_thing(x: u32, y: String, z: f64) -> &'static str {
///     "yepperz"
/// }
///
/// let _ctx = Ctx::default()
///     // inline with get_with:
///     .get_with(uri!["the-thing"], formr::<R![x: _, y: _, z: _]>, the_thing)
///     // or as a middleware:
///     .try_then(formr::<R![x: _, y: _]>)
///     .get(uri!["the-thing" / z: f64], the_thing);
/// ```
pub async fn formr<T: IsoDecode>(cx: R![Body]) -> Result<T, FormBodyError> {
    let bodyr = body::aggregate(cx.head).await?.reader();

    serde_urlencoded::from_reader(bodyr)
        .map_err(FormBodyError::Form)
        .map(T::from_repr)
}

/// An error encountered during automatic deserialization of a request body.
#[derive(Debug, Error)]
pub enum AutoBodyError {
    /// There wasn't a content type header to determine a deserializer.
    #[error("failed to determine format")]
    MissingContentType,

    /// An unknown format was specified.
    #[error("unknown format: {}", .0)]
    UnknownFormat(Mime),

    /// Error encountered while reading the request body.
    #[error("failed to read body: {}", .0)]
    Body(#[from] hyper::Error),

    /// Error occurred during json deserialization.
    #[error("failed to parse body: {}", .0)]
    Json(#[from] serde_json::Error),

    /// Error occurred during form deserialization.
    #[error("failed to parse body: {}", .0)]
    Form(#[from] serde_urlencoded::de::Error),
}

bad_request_display! { AutoBodyError }

/// Deserialize a value from the request body, using the `Content-Type` header to determine the
/// serialization format.
///
/// Use with [`Ctx::handle_with`][super::Ctx::handle_with] or [`Ctx::try_then`][super::Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::auto, record_args, uri, Ctx};
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct ThingRequest {
///     x: u32,
///     y: String,
/// }
///
/// #[record_args]
/// async fn the_thing(_: ThingRequest) -> &'static str {
///     "yepperz"
/// }
///
/// let _ctx = Ctx::default()
///     // inline with get_with:
///     .get_with(uri!["the-thing"], auto::<ThingRequest>, the_thing)
///     // or as a middleware:
///     .try_then(auto::<ThingRequest>)
///     .get(uri!["the-thing" / "via-mw"], the_thing);
/// ```
pub async fn auto<T>(cx: R![Body, HeaderMap]) -> Result<R![T, HeaderMap], AutoBodyError>
where T: DeserializeOwned {
    let (head, tail) = (cx.head, cx.tail);

    let mime: Mime = (tail.head)
        .typed_get::<ContentType>()
        .ok_or(AutoBodyError::MissingContentType)?
        .into();

    let bodyr = body::aggregate(head).await?.reader();

    match mime.subtype() {
        mime::JSON => serde_json::from_reader(bodyr)
            .map_err(AutoBodyError::Json)
            .map(|t| tail.prepend(t)),

        mime::WWW_FORM_URLENCODED => serde_urlencoded::from_reader(bodyr)
            .map_err(AutoBodyError::Form)
            .map(|t| tail.prepend(t)),

        _ => Err(AutoBodyError::UnknownFormat(mime)),
    }
}

/// Deserialize an anonymous record from the request body, using the `Content-Type` header to
/// determine the serialization format.
///
/// This can be used to specify a request body without declaring a bespoke request struct,
/// while maintaining type safe access to the payload.
///
/// Any fields of the record will be merged into the context's state as if they were provided
/// inline.
///
/// Use with [`Ctx::handle_with`][super::Ctx::handle_with] or [`Ctx::try_then`][super::Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::autor, record_args, uri, Ctx, R};
///
/// #[record_args]
/// async fn the_thing(x: u32, y: String, z: f64) -> &'static str {
///     "yepperz"
/// }
///
/// let _ctx = Ctx::default()
///     // inline with get_with:
///     .get_with(uri!["the-thing"], autor::<R![x: _, y: _, z: _]>, the_thing)
///     // or as a middleware:
///     .try_then(autor::<R![x: _, y: _]>)
///     .get(uri!["the-thing" / z: f64], the_thing);
/// ```
pub async fn autor<T>(cx: R![Body, HeaderMap]) -> Result<HCons<HeaderMap, T>, AutoBodyError>
where T: HList + IsoDecode {
    let (head, tail) = (cx.head, cx.tail);

    let mime: Mime = (tail.head)
        .typed_get::<ContentType>()
        .ok_or(AutoBodyError::MissingContentType)?
        .into();

    let bodyr = body::aggregate(head).await?.reader();

    match mime.subtype() {
        mime::JSON => serde_json::from_reader(bodyr)
            .map_err(AutoBodyError::Json)
            .map(|t| T::from_repr(t).prepend(tail.head)),

        mime::WWW_FORM_URLENCODED => serde_urlencoded::from_reader(bodyr)
            .map_err(AutoBodyError::Form)
            .map(|t| T::from_repr(t).prepend(tail.head)),

        _ => Err(AutoBodyError::UnknownFormat(mime)),
    }
}

bad_request_display! { hyper::Error }

/// Retrieve the request body as a contiguous [Bytes] buffer.
///
/// Use with [`Ctx::handle_with`][super::Ctx::handle_with] or [`Ctx::try_then`][super::Ctx::try_then].
///
/// # Examples
/// ```
/// use bytes::Bytes;
/// use hyperbole::{body, record_args, uri, Ctx};
///
/// #[record_args]
/// async fn the_thing(_body: Bytes) -> &'static str {
///     "got em"
/// }
///
/// let _ctx = Ctx::default()
///     // inline with get_with:
///     .get_with(uri!["the-thing"], body::bytes, the_thing)
///     // or as a middleware:
///     .try_then(body::bytes)
///     .get(uri!["eht-thing"], the_thing);
/// ```
pub async fn bytes(cx: R![Body]) -> hyper::Result<R![Bytes]> {
    body::to_bytes(cx.head).await.map(|b| r![b])
}

/// Retrieve the request body as a non-contiguous [Buffer].
///
/// Use with [`Ctx::handle_with`][super::Ctx::handle_with] or [`Ctx::try_then`][super::Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{
///     body::{self, Buffer},
///     record_args, uri, Ctx,
/// };
///
/// #[record_args]
/// async fn the_thing(_body: Buffer) -> &'static str {
///     "got em"
/// }
///
/// let _ctx = Ctx::default()
///     // inline with get_with:
///     .get_with(uri!["the-thing"], body::aggregate, the_thing)
///     // or as a middleware:
///     .try_then(body::aggregate)
///     .get(uri!["eht-thing"], the_thing);
/// ```
// TODO: this should be an async fn, but rustdoc can't handle that with a type_alias_impl_trait
//       binding for some reason.
pub fn aggregate(cx: R![Body]) -> impl Future<Output = hyper::Result<R![Buffer]>> {
    body::aggregate(cx.head).map(|h| h.map(|b| r![b]))
}

/// The opaque [Buf] returned by [aggregate].
pub type Buffer = impl Buf;
