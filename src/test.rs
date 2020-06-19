//! Facilities for testing hyperbole apps.
use super::App;
use hyper::{
    body::{to_bytes, Bytes},
    Body, Method, Request, Response,
};
use serde::{de::DeserializeOwned, Serialize};

const LOCAL: ([u8; 4], u16) = ([127, 0, 0, 1], 4321);

#[inline]
fn request(m: Method, path: &str) -> Request<Body> {
    assert!(path.starts_with('/'));

    Request::builder()
        .method(m)
        .uri(format!("http://testclient{}", path))
        .body(Body::empty())
        .unwrap()
}

/// A test client.
pub struct Client<I> {
    pub(super) app: App<I>,
}

impl<I: Sync + Send + Clone + 'static> Client<I> {
    /// Prepare a call with the provided `method` and `path`.
    pub fn call<'a>(&'a self, method: Method, path: &str) -> Call<'a, I> {
        Call {
            app: &self.app,
            req: request(method, path),
        }
    }

    /// Prepare a GET call with the provided `path`.
    pub fn get<'a>(&'a self, path: &str) -> Call<'a, I> {
        self.call(Method::GET, path)
    }

    /// Prepare a POST call with the provided `path`.
    pub fn post<'a>(&'a self, path: &str) -> Call<'a, I> {
        self.call(Method::POST, path)
    }

    /// Prepare a PUT call with the provided `path`.
    pub fn put<'a>(&'a self, path: &str) -> Call<'a, I> {
        self.call(Method::PUT, path)
    }

    /// Prepare a PATCH call with the provided `path`.
    pub fn patch<'a>(&'a self, path: &str) -> Call<'a, I> {
        self.call(Method::PATCH, path)
    }

    /// Prepare a DELETE call with the provided `path`.
    pub fn delete<'a>(&'a self, path: &str) -> Call<'a, I> {
        self.call(Method::DELETE, path)
    }
}

/// A test call.
pub struct Call<'a, I> {
    app: &'a App<I>,
    req: Request<Body>,
}

impl<'a, I: Sync + Send + Clone + 'static> Call<'a, I> {
    /// Set a request body for this call.
    pub fn body<B: Into<Body>>(mut self, body: B) -> Self {
        *self.req.body_mut() = body.into();
        self
    }

    /// Set a json request body for this call.
    pub fn body_json<T: Serialize>(mut self, body: &T) -> Self {
        *self.req.body_mut() = serde_json::to_vec(body).unwrap().into();
        self
    }

    /// Dispatch the request defined by this call.
    pub async fn dispatch_body(self) -> Response<Body> {
        self.app.dispatch(self.req, LOCAL.into()).await
    }

    /// Dispatch the request defined by this call, retrieving the response body as a [Bytes].
    pub async fn dispatch_bytes(self) -> Response<Bytes> {
        let (parts, body) = self.dispatch_body().await.into_parts();
        let bytes = to_bytes(body).await.unwrap();

        Response::from_parts(parts, bytes)
    }

    /// Dispatch the request defined by this call, retrieving the response body as a [String].
    pub async fn dispatch(self) -> Response<String> {
        self.dispatch_bytes()
            .await
            .map(|b| String::from_utf8_lossy(&*b).into_owned())
    }

    /// Dispatch the request defined by this call, retrieving the response body as a decoded
    /// json object.
    pub async fn dispatch_json<T: DeserializeOwned>(self) -> Response<T> {
        self.dispatch_bytes()
            .await
            .map(|b| serde_json::from_slice(&*b).unwrap())
    }
}
