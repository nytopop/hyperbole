use hyper::body::to_bytes;
use hyperbole::{reply::Reply, *};

#[tokio::test]
async fn test_json_response() {
    let app = App::new()
        .context()
        .get(path![x: u32 / y: f64], |cx: R![x: _, y: _]| async move {
            reply::jsonr(&cx)
        })
        .collapse()
        .test_client();

    let r = app.get("/44/55").dispatch().await;
    assert_eq!(r#"{"x":44,"y":55.0}"#, r.body());
    assert!(r.status().is_success());
}

#[tokio::test]
async fn test_jsonr_errors() {
    let input = r#"{"a":3,"b":32324,"c":345345.34}"#;

    let res = body::jsonr::<R![a: String, b: u32, c: f32]>(r![input.into()])
        .await
        .unwrap_err();

    let body = res.into_response().into_body();
    let raw = to_bytes(body).await.unwrap();

    assert_eq!(
        "failed to parse body: invalid type: integer `3`, expected a string at line 1 column 31",
        String::from_utf8_lossy(&*raw).into_owned(),
    );
}
