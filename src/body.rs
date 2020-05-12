//! Helpers for parsing request bodies.
use super::{field::IsoDecode, reply::Reply, Response};
use bytes::buf::BufExt;
use frunk_core::{hlist, Hlist};
use hyper::{Body, StatusCode};
use serde::de::DeserializeOwned;

/// An error encountered during json deserialization of a request body.
#[derive(Debug)]
pub enum JsonBodyError {
    /// Error occurred while reading the request body.
    Body(hyper::Error),
    /// Error occurred during deserialization.
    Json(serde_json::Error),
}

impl Reply for JsonBodyError {
    #[inline]
    fn into_response(self) -> Response {
        let err = match self {
            JsonBodyError::Body(e) => format!("failed to read body: {}", e),
            JsonBodyError::Json(e) => format!("failed to parse body as json: {}", e),
        };

        hyper::Response::builder()
            .status(StatusCode::BAD_REQUEST)
            .body(err.into())
            .unwrap()
    }
}

/// Deserialize a value from a json request body.
///
/// # Examples
/// ```
/// use hyperbole::{body::json, path, App, Hlist};
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct ThingRequest {
///     x: u32,
///     y: String,
/// }
///
/// async fn the_thing(_: Hlist![ThingRequest]) -> &'static str {
///     "yepperz"
/// }
///
/// let _app = App::empty()
///     .context()
///     // inline with get_with:
///     .get_with(path!["the-thing"], json::<ThingRequest>, the_thing)
///     // or as a middleware:
///     .try_then(json::<ThingRequest>)
///     .get(path!["the-thing" / "via-mw"], the_thing)
///     .collapse();
/// ```
pub async fn json<T: DeserializeOwned>(cx: Hlist![Body]) -> Result<Hlist![T], Box<JsonBodyError>> {
    let bodyr = hyper::body::aggregate(cx.head)
        .await
        .map_err(JsonBodyError::Body)
        .map_err(Box::new)?
        .reader();

    serde_json::from_reader(bodyr)
        .map_err(JsonBodyError::Json)
        .map_err(Box::new)
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
/// The serialization format of records is equivalent to a struct with the same fields:
///
/// ```
/// use hyperbole::{field::IsoEncode, record};
/// use serde::Serialize;
///
/// #[derive(Serialize)]
/// struct MyRequest {
///     a: String,
///     b: u32,
///     c: f32,
/// }
///
/// let my_req = serde_json::to_string(&MyRequest {
///     a: "hello-worldo".into(),
///     b: 32324,
///     c: 345345.34,
/// })
/// .unwrap();
///
/// let my_req_r = serde_json::to_string(
///     &record! {
///         a = "hello-worldo".to_string(),
///         b = 32324,
///         c = 345345.34,
///     }
///     .as_repr(),
/// )
/// .unwrap();
///
/// // both of the above serialize to:
/// let repr = r#"{"a":"hello-worldo","b":32324,"c":345345.34}"#;
///
/// assert_eq!(repr, my_req);
/// assert_eq!(repr, my_req_r);
/// ```
///
/// Use with [Ctx::handle_with] or [Ctx::try_then].
///
/// # Examples
/// ```
/// use hyperbole::{body::jsonr, path, record, App};
///
/// async fn the_thing(_: record![x: u32, y: String, z: f64]) -> &'static str {
///     "yepperz"
/// }
///
/// let _app = App::empty()
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
pub async fn jsonr<T: IsoDecode>(cx: Hlist![Body]) -> Result<T, Box<JsonBodyError>> {
    let bodyr = hyper::body::aggregate(cx.head)
        .await
        .map_err(JsonBodyError::Body)
        .map_err(Box::new)?
        .reader();

    serde_json::from_reader(bodyr)
        .map_err(JsonBodyError::Json)
        .map_err(Box::new)
        .map(T::from_repr)
}

// TODO: form + multipart form
// TODO: record variants of ^

#[cfg(test)]
mod tests {
    use super::{super::record, *};
    use hyper::body::to_bytes;

    async fn reply_str<R: Reply>(r: R) -> String {
        let body = r.into_response().into_body();
        let bin = to_bytes(body).await.unwrap();

        String::from_utf8_lossy(&*bin).into_owned()
    }

    #[tokio::test]
    async fn test_jsonr_errors() {
        let input = r#"{"a":3,"b":32324,"c":345345.34}"#;

        let res = jsonr::<record![a: String, b: u32, c: f32,]>(hlist![input.into()])
            .await
            .unwrap_err();
        let body = reply_str(res).await;

        assert_eq!(
            "failed to parse body as json: invalid type: integer `3`, expected a string at line 1 column 31",
            body
        );
    }
}
