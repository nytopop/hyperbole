use hyper::Body;
use hyperbole::*;

#[test]
fn test_modify_uri_parser_after_erasure() {
    let _ = App::new()
        .context()
        .map(|_: Hlist![Body]| record![])
        .map(|_: record![]| record![foo = 40u64])
        .path(path![bar: u32])
        .map(|_: record![bar, foo]| record![])
        .collapse();

    let _ = App::new()
        .context()
        .inject(f![x = 40])
        .map(|_: record![x]| record![])
        .path(path![y: u32])
        .map(|_: record![y]| record![])
        .collapse();

    let _ = App::new()
        .context()
        .map(|_: record![]| record![x = 40])
        .map(|cx: record![x]| cx)
        .path(path![y: u32])
        .map(|_: record![y]| record![])
        .collapse();
}

#[tokio::test]
async fn test_basic_uri_parsing() {
    async fn handle(cx: record![x: u32, y: f64]) -> String {
        let (x, y) = cx.into();
        format!("x: {}, y: {}", x, y)
    }

    let app = App::new()
        .context_path(path![x: u32 / y: f64])
        .get(path![], handle)
        .collapse()
        .test_client();

    let r = app.get("/44/55").dispatch().await;
    assert_eq!("x: 44, y: 55", r.body());
    assert!(r.status().is_success());

    let r = app.get("/more/fdfdf").dispatch().await;
    assert_eq!(
        r#"failed to parse "more" in uri: invalid digit found in string"#,
        r.body()
    );
    assert!(r.status().is_client_error());

    let r = app.get("/4848484/fdfdf").dispatch().await;
    assert_eq!(
        r#"failed to parse "fdfdf" in uri: invalid float literal"#,
        r.body()
    );
    assert!(r.status().is_client_error());
}

#[tokio::test]
async fn test_route_dispatch_with_ctx_val() {
    async fn handle(cx: record![val: u32]) -> String {
        format!("{}", *cx.head)
    }

    let app = App::new()
        .context()
        .map(|_: record![]| record![val = 0])
        .get(path!["a"], handle)
        .map(|_: record![val]| record![val = 1])
        .get(path!["b"], handle)
        .map(|_: record![val]| record![val = 2])
        .get(path!["c"], handle)
        .map(|_: record![val]| record![val = 3])
        .get(path!["d"], handle)
        .map(|_: record![val]| record![val = 4])
        .get(path!["e"], handle)
        .map(|_: record![val]| record![val = 5])
        .get(path!["f"], handle)
        .collapse()
        .test_client();

    for (path, val) in vec![
        ("/a", 0u32),
        ("/b", 1),
        ("/c", 2),
        ("/d", 3),
        ("/e", 4),
        ("/f", 5),
    ] {
        let r = app.get(path).dispatch().await;

        assert_eq!(&format!("{}", val), r.body());
        assert!(r.status().is_success());
    }
}
