//! Helpers for replying to requests.
use super::Response;
use frunk_core::coproduct::{CNil, Coproduct};
use headers::{Header, HeaderMapExt};
use hyper::{
    header::{CONTENT_TYPE, X_CONTENT_TYPE_OPTIONS},
    StatusCode,
};
use std::{borrow::Cow, convert::Infallible};

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

impl Reply for Infallible {
    #[inline]
    fn into_response(self) -> Response {
        match self {}
    }
}

impl Reply for Response {
    #[inline]
    fn into_response(self) -> Response {
        self
    }
}

impl<R: Reply, E: Reply> Reply for Result<R, E> {
    #[inline]
    fn into_response(self) -> Response {
        self.map_or_else(E::into_response, R::into_response)
    }
}

impl Reply for CNil {
    #[inline]
    fn into_response(self) -> Response {
        match self {}
    }
}

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
