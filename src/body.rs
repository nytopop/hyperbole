//! Helpers for parsing request bodies.
use super::{field::IsoDecode, reply::Reply, Response};
use bytes::buf::BufExt;
use frunk_core::{
    hlist,
    hlist::{HCons, HList},
    Hlist,
};
use headers::{ContentType, HeaderMapExt};
use http::HeaderMap;
use hyper::{body::aggregate, Body, StatusCode};
use mime::Mime;
use serde::de::DeserializeOwned;
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
/// Use with [Ctx::handle_with] or [Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::json, path, record_args, App};
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
/// let _app = App::new()
///     .context()
///     // inline with get_with:
///     .get_with(path!["the-thing"], json::<ThingRequest>, the_thing)
///     // or as a middleware:
///     .try_then(json::<ThingRequest>)
///     .get(path!["the-thing" / "via-mw"], the_thing)
///     .collapse();
/// ```
///
/// [Ctx::handle_with]: super::Ctx::handle_with
/// [Ctx::try_then]: super::Ctx::try_then
pub async fn json<T: DeserializeOwned>(cx: Hlist![Body]) -> Result<Hlist![T], JsonBodyError> {
    let bodyr = aggregate(cx.head).await?.reader();

    serde_json::from_reader(bodyr)
        .map_err(JsonBodyError::Json)
        .map(|t| hlist![t])
}

/// Deserialize an anonymous record from a json request body.
///
/// This can be used to specify a request body without declaring a bespoke request struct,
/// while maintaining type safe access to the payload.
///
/// Any fields of the record will be merged into the context's state as if they were provided
/// inline.
///
/// Use with [Ctx::handle_with] or [Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::jsonr, path, record, record_args, App};
///
/// #[record_args]
/// async fn the_thing(x: u32, y: String, z: f64) -> &'static str {
///     "yepperz"
/// }
///
/// let _app = App::new()
///     .context()
///     // inline with get_with:
///     .get_with(path!["the-thing"], jsonr::<record![x, y, z]>, the_thing)
///     // or as a middleware:
///     .try_then(jsonr::<record![x, y]>)
///     .get(path!["the-thing" / z: f64], the_thing)
///     .collapse();
/// ```
///
/// [Ctx::handle_with]: super::Ctx::handle_with
/// [Ctx::try_then]: super::Ctx::try_then
pub async fn jsonr<T: IsoDecode>(cx: Hlist![Body]) -> Result<T, JsonBodyError> {
    let bodyr = aggregate(cx.head).await?.reader();

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
/// Use with [Ctx::handle_with] or [Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::form, path, record_args, App};
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
/// let _app = App::new()
///     .context()
///     // inline with get_with:
///     .get_with(path!["the-thing"], form::<ThingRequest>, the_thing)
///     // or as a middleware:
///     .try_then(form::<ThingRequest>)
///     .get(path!["the-thing" / "via-mw"], the_thing)
///     .collapse();
/// ```
///
/// [Ctx::handle_with]: super::Ctx::handle_with
/// [Ctx::try_then]: super::Ctx::try_then
pub async fn form<T: DeserializeOwned>(cx: Hlist![Body]) -> Result<Hlist![T], FormBodyError> {
    let bodyr = aggregate(cx.head).await?.reader();

    serde_urlencoded::from_reader(bodyr)
        .map_err(FormBodyError::Form)
        .map(|t| hlist![t])
}

/// Deserialize an anonymous record from an `x-www-form-urlencoded` request body.
///
/// This can be used to specify a request body without declaring a bespoke request struct,
/// while maintaining type safe access to the payload.
///
/// Any fields of the record will be merged into the context's state as if they were provided
/// inline.
///
/// Use with [Ctx::handle_with] or [Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::formr, path, record, record_args, App};
///
/// #[record_args]
/// async fn the_thing(x: u32, y: String, z: f64) -> &'static str {
///     "yepperz"
/// }
///
/// let _app = App::new()
///     .context()
///     // inline with get_with:
///     .get_with(path!["the-thing"], formr::<record![x, y, z]>, the_thing)
///     // or as a middleware:
///     .try_then(formr::<record![x, y]>)
///     .get(path!["the-thing" / z: f64], the_thing)
///     .collapse();
/// ```
///
/// [Ctx::handle_with]: super::Ctx::handle_with
/// [Ctx::try_then]: super::Ctx::try_then
pub async fn formr<T: IsoDecode>(cx: Hlist![Body]) -> Result<T, FormBodyError> {
    let bodyr = aggregate(cx.head).await?.reader();

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
/// Use with [Ctx::handle_with] or [Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::auto, path, record_args, App};
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
/// let _app = App::new()
///     .context()
///     // inline with get_with:
///     .get_with(path!["the-thing"], auto::<ThingRequest>, the_thing)
///     // or as a middleware:
///     .try_then(auto::<ThingRequest>)
///     .get(path!["the-thing" / "via-mw"], the_thing)
///     .collapse();
/// ```
///
/// [Ctx::handle_with]: super::Ctx::handle_with
/// [Ctx::try_then]: super::Ctx::try_then
pub async fn auto<T>(cx: Hlist![Body, HeaderMap]) -> Result<Hlist![T, HeaderMap], AutoBodyError>
where T: DeserializeOwned {
    let (head, tail) = (cx.head, cx.tail);

    let mime: Mime = (tail.head)
        .typed_get::<ContentType>()
        .ok_or(AutoBodyError::MissingContentType)?
        .into();

    let bodyr = aggregate(head).await?.reader();

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
/// Use with [Ctx::handle_with] or [Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::autor, path, record, record_args, App};
///
/// #[record_args]
/// async fn the_thing(x: u32, y: String, z: f64) -> &'static str {
///     "yepperz"
/// }
///
/// let _app = App::new()
///     .context()
///     // inline with get_with:
///     .get_with(path!["the-thing"], autor::<record![x, y, z]>, the_thing)
///     // or as a middleware:
///     .try_then(autor::<record![x, y]>)
///     .get(path!["the-thing" / z: f64], the_thing)
///     .collapse();
/// ```
///
/// [Ctx::handle_with]: super::Ctx::handle_with
/// [Ctx::try_then]: super::Ctx::try_then
pub async fn autor<T>(cx: Hlist![Body, HeaderMap]) -> Result<HCons<HeaderMap, T>, AutoBodyError>
where T: HList + IsoDecode {
    let (head, tail) = (cx.head, cx.tail);

    let mime: Mime = (tail.head)
        .typed_get::<ContentType>()
        .ok_or(AutoBodyError::MissingContentType)?
        .into();

    let bodyr = aggregate(head).await?.reader();

    match mime.subtype() {
        mime::JSON => serde_json::from_reader(bodyr)
            .map_err(AutoBodyError::Json)
            .map(T::from_repr)
            .map(|t| t.prepend(tail.head)),

        mime::WWW_FORM_URLENCODED => serde_urlencoded::from_reader(bodyr)
            .map_err(AutoBodyError::Form)
            .map(T::from_repr)
            .map(|t| t.prepend(tail.head)),

        _ => Err(AutoBodyError::UnknownFormat(mime)),
    }
}
