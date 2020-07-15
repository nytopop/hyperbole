//! A simple api that does some math.
use hyper::server::Server;
use hyperbole::{record_args, uri, App, R};

#[record_args]
async fn mul(a: f64, b: f64) -> String {
    format!("{}\n", a * b)
}

#[record_args]
async fn div(a: f64, b: f64) -> String {
    format!("{}\n", a / b)
}

#[tokio::main]
async fn main() -> hyper::Result<()> {
    let app = App::new()
        .context_path(uri![a: f64 / b: f64])
        .get(uri!["add"], |cx: R![a: _, b: _]| async move {
            let (a, b) = cx.into();
            format!("{}\n", *a + *b)
        })
        .get(uri!["sub"], |cx: R![a: _, b: _]| async move {
            let (a, b) = cx.into();
            format!("{}\n", *a - *b)
        })
        .get(uri!["mul"], mul)
        .get(uri!["div"], div)
        .collapse();

    Server::bind(&([127, 0, 0, 1], 8080).into())
        .serve(app.into_make_service())
        .await
}
