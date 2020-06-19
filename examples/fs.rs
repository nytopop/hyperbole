//! A static fileserver.
use hyper::server::Server;
use hyperbole::{mw, App};

#[tokio::main]
async fn main() -> hyper::Result<()> {
    let app = App::empty().not_found(mw::filesystem("."));

    Server::bind(&([127, 0, 0, 1], 8080).into())
        .serve(app.into_make_service())
        .await
}
