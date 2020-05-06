//! A simple api that does some math.
use hyper::server::Server;
use hyperbole::{path, record, App};

async fn mul(cx: record![a: f64, b: f64]) -> String {
    let (a, b) = cx.into();
    format!("{}\n", *a * *b)
}

async fn div(cx: record![a: f64, b: f64]) -> String {
    let (a, b) = cx.into();
    format!("{}\n", *a / *b)
}

#[tokio::main]
async fn main() -> hyper::Result<()> {
    let app = App::empty()
        .context_path(path![a: f64 / b: f64])
        .get(path!["add"], |cx: record![a, b]| async move {
            let (a, b) = cx.into();
            format!("{}\n", *a + *b)
        })
        .get(path!["sub"], |cx: record![b, a]| async move {
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
