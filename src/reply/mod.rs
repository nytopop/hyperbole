//! Helpers for replying to requests.
use super::{field::IsoEncode, Response, R};
use frunk_core::coproduct::{CNil, Coproduct};
use headers::{Header, HeaderMapExt};
use http::{HeaderMap, Method, StatusCode, Uri};
use hyper::{
    header::{CONTENT_TYPE, LOCATION, X_CONTENT_TYPE_OPTIONS},
    Body,
};
use hyper_staticfile::{resolve_path, ResponseBuilder};
use serde::Serialize;
use std::{
    borrow::Cow,
    convert::{Infallible, TryFrom},
    future::Future,
    io,
    path::PathBuf,
};
use thiserror::Error;

pub mod sse;

/// A type that can be converted into an http [Response].
pub trait Reply: Sized + Send {
    /// Perform the conversion.
    fn into_response(self) -> Response;

    /// Change the status code to `code`.
    ///
    /// ```
    /// use hyper::StatusCode;
    /// use hyperbole::{reply::Reply, Response};
    ///
    /// let _: Response = "some message" //
    ///     .with_status(StatusCode::OK);
    /// ```
    #[inline]
    fn with_status(self, code: StatusCode) -> Response {
        let mut resp = self.into_response();
        *resp.status_mut() = code;
        resp
    }

    /// Include a typed `header` in the response.
    ///
    /// ```
    /// use headers::ContentType;
    /// use hyperbole::{reply::Reply, Response};
    ///
    /// let _: Response = "some message" //
    ///     .with_header(ContentType::text());
    /// ```
    #[inline]
    fn with_header<H: Header>(self, header: H) -> Response {
        let mut resp = self.into_response();
        resp.headers_mut().typed_insert(header);
        resp
    }
}

impl Reply for Response {
    #[inline]
    fn into_response(self) -> Response {
        self
    }

    #[inline]
    fn with_status(mut self, code: StatusCode) -> Response {
        *self.status_mut() = code;
        self
    }

    #[inline]
    fn with_header<H: Header>(mut self, header: H) -> Response {
        self.headers_mut().typed_insert(header);
        self
    }
}

impl<R: Reply, E: Reply> Reply for Result<R, E> {
    #[inline]
    fn into_response(self) -> Response {
        self.map_or_else(E::into_response, R::into_response)
    }
}

macro_rules! uninhabited {
    ($t: ty) => {
        impl Reply for $t {
            #[inline]
            fn into_response(self) -> Response {
                match self {}
            }
        }
    };
}

uninhabited! { Infallible }

uninhabited! { CNil }

impl<H: Reply, Tail: Reply> Reply for Coproduct<H, Tail> {
    #[inline]
    fn into_response(self) -> Response {
        match self {
            Coproduct::Inl(h) => h.into_response(),
            Coproduct::Inr(t) => t.into_response(),
        }
    }
}

impl<T: Reply> Reply for Box<T> {
    #[inline]
    fn into_response(self) -> Response {
        (*self).into_response()
    }
}

impl<'a, T: ToOwned> Reply for Cow<'a, T>
where
    &'a T: Reply,
    T::Owned: Reply,
{
    #[inline]
    fn into_response(self) -> Response {
        match self {
            Cow::Borrowed(t) => t.into_response(),
            Cow::Owned(t) => t.into_response(),
        }
    }
}

macro_rules! content_type {
    ($mime:literal $( $re_type:ty ),+ $(,)?) => {
        $(impl Reply for $re_type {
            #[inline]
            fn into_response(self) -> Response {
                hyper::Response::builder()
                    .header(CONTENT_TYPE, $mime)
                    .header(X_CONTENT_TYPE_OPTIONS, "nosniff")
                    .body(self.into())
                    .unwrap()
            }
        })+
    };
}

content_type! { "text/plain; charset=utf-8"
    String,
    &'static str,
}

content_type! { "application/octet-stream"
    Vec<u8>,
    &'static [u8],
}

/// Returns a json [Response] from an arbitrary serializable value.
#[inline]
pub fn json<T: Serialize>(value: &T) -> Response {
    let ser = serde_json::to_string(value).unwrap();

    hyper::Response::builder()
        .header(CONTENT_TYPE, "application/json")
        .header(X_CONTENT_TYPE_OPTIONS, "nosniff")
        .body(ser.into())
        .unwrap()
}

/// Returns a json [Response] from an hlist of [Serialize] named fields.
///
/// # Examples
/// ```
/// use hyperbole::{r, reply};
///
/// let _ = reply::jsonr(&r![
///     a = "cool",
///     b = 44,
///     c = 3.03,
///     d = "hello worldo",
///     e = "more"
/// ]);
/// ```
#[inline]
pub fn jsonr<'a, T: IsoEncode<'a>>(value: &'a T) -> Response {
    json(&value.as_repr())
}

/// Handle a request by extracting a [Reply] from the request context.
///
/// This can be used to terminate a middleware chain if handling a request doesn't require
/// any extra logic.
///
/// # Examples
/// ```
/// use hyperbole::{f, r, reply, uri, Ctx, R};
///
/// let _ctx = Ctx::default()
///     .map(|_: R![]| r!["this is my response"])
///     .get(uri!["i-want-my-str"], reply::extract::<&str>)
///     .map(|_: R![]| r![foo = "here is fresh foo"])
///     .get(uri!["unhand-me-a-foo"], reply::extract::<f![foo]>);
/// ```
pub async fn extract<T: Reply>(cx: R![T]) -> T {
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

/// Handle a request by serving a file from the filesystem. The file path to be served will be the
/// request uri path appended to `base_path`.
///
/// # Examples
/// ```
/// use hyperbole::{reply, uri, App};
///
/// let _app = App::new()
///     .not_found(reply::filesystem("/srv"))
///     .context()
///     .get(uri!["a" / "whatever.jpg"], reply::filesystem("/srv"))
///     .get(uri!["b" / *extra: String], reply::filesystem("/opt"))
///     .collapse();
/// ```
pub fn filesystem(base_path: &str) -> impl Fn(R![Method, Uri, HeaderMap]) -> FsFuture {
    let root = PathBuf::from(base_path);

    move |cx| fs_inner(root.clone(), cx.head, Ok(cx.tail.head), cx.tail.tail.head)
}

/// Handle a request by serving a file from the filesystem. Unlike [filesystem], the file path to
/// be served will be the named field `path: String` appended to `base_path`.
///
/// # Examples
/// ```
/// use hyperbole::{r, reply, uri, Ctx, R};
///
/// let _ctx = Ctx::default()
///     // use a uri! parser to extract `path: String` from the uri
///     .get(uri!["css" / *path: String], reply::filesystem_path("/srv"))
///     // or populate `path: String` in a middleware
///     .map(|cx: R![]| r![path = "an-image-file.jpg".to_owned()])
///     .get(uri!["image"], reply::filesystem_path("/srv"));
/// ```
pub fn filesystem_path(
    base_path: &str,
) -> impl Fn(R![Method, path: String, HeaderMap]) -> FsFuture {
    let root = PathBuf::from(base_path);

    move |cx| {
        let uri = Uri::try_from(cx.tail.head.into_inner()).map_err(|e| e.into());
        fs_inner(root.clone(), cx.head, uri, cx.tail.tail.head)
    }
}

/// The opaque [Future] returned by [filesystem] and [filesystem_path].
pub type FsFuture = impl Future<Output = Result<Response, FsError>>;

type UriRes = http::Result<Uri>;

async fn fs_inner(path: PathBuf, m: Method, u: UriRes, h: HeaderMap) -> Result<Response, FsError> {
    let uri = u?;

    ResponseBuilder::new()
        .request_parts(&m, &uri, &h)
        .build(resolve_path(path, uri.path()).await?)
        .map_err(|e| e.into())
}

/// Returns a redirect response to the provided `path`.
///
/// # Examples
/// ```
/// use hyperbole::{reply, uri, Ctx, R};
///
/// let _ctx = Ctx::default().get(uri!["go-home"], |cx: R![]| async {
///     reply::redirect(true, "/home")
/// });
/// ```
pub fn redirect<P: AsRef<str>>(permanent: bool, path: P) -> Response {
    hyper::Response::builder()
        .status(if permanent {
            StatusCode::PERMANENT_REDIRECT
        } else {
            StatusCode::TEMPORARY_REDIRECT
        })
        .header(LOCATION, path.as_ref())
        .body(Body::empty())
        .unwrap()
}
