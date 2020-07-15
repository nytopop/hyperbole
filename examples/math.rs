//! A simple api that does some math.
use hyper::server::Server;
use hyperbole::{path, record_args, App, R};

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
        .context_path(path![a: f64 / b: f64])
        .get(path!["add"], |cx: R![a: _, b: _]| async move {
            let (a, b) = cx.into();
            format!("{}\n", *a + *b)
        })
        .get(path!["sub"], |cx: R![a: _, b: _]| async move {
            let (a, b) = cx.into();
            format!("{}\n", *a - *b)
        })
        .get(path!["mul"], mul)
        .get(path!["div"], div)
        .collapse();

    Server::bind(&([127, 0, 0, 1], 8080).into())
        .serve(app.into_make_service())
        .await
}
