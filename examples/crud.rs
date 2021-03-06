//! A simple json CRUD api.
#![allow(clippy::option_map_unit_fn)]
use hyper::{server::Server, StatusCode};
use hyperbole::{
    body::jsonr,
    f, r, record_args,
    reply::{self, Reply},
    uri, App, Response, R,
};
use serde::Serialize;
use std::{
    collections::BTreeMap,
    num::ParseIntError,
    ops::{Bound, RangeBounds},
    str::FromStr,
    sync::Arc,
};
use thiserror::Error;
use tokio::sync::Mutex;

#[derive(Debug, Error)]
enum InvalidIdRange {
    #[error("invalid id range")]
    Bounds,
    #[error("{}", .0)]
    Num(#[from] ParseIntError),
}

#[derive(Copy, Clone, Default)]
struct IdRange(Option<u64>, Option<u64>);

impl RangeBounds<u64> for IdRange {
    fn start_bound(&self) -> Bound<&u64> {
        (self.0.as_ref())
            .map(Bound::Included)
            .unwrap_or(Bound::Unbounded)
    }

    fn end_bound(&self) -> Bound<&u64> {
        (self.1.as_ref())
            .map(Bound::Excluded)
            .unwrap_or(Bound::Unbounded)
    }
}

impl FromStr for IdRange {
    type Err = InvalidIdRange;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let "" | ".." = s {
            return Ok(IdRange::default());
        }
        if let Some(s) = s.strip_suffix("..") {
            return Ok(IdRange(Some(s.parse()?), None));
        }
        if let Some(s) = s.strip_prefix("..") {
            return Ok(IdRange(None, Some(s.parse()?)));
        }
        match s.find("..") {
            Some(i) => Ok(IdRange(Some(s[..i].parse()?), Some(s[i + 2..].parse()?))),
            None => Err(InvalidIdRange::Bounds),
        }
    }
}

#[tokio::main]
async fn main() -> hyper::Result<()> {
    let app = App::new()
        .context_path(uri!["widgets"])
        .inject(f![db = Db::default()])
        // POST /widgets/new
        .post_with(uri!["new"], jsonr::<R![name: _, desc: _, count: _]>, new)
        // GET /widgets
        // GET /widgets?range=4..30
        .get(uri![? range: IdRange], list)
        .path(uri![id: u64])
        // GET /widgets/:id
        .get(uri![], get)
        // PATCH /widgets/:id {"name": "blabla", "desc": null, "count": 40}
        .patch_with(uri![], jsonr::<R![name: _, desc: _, count: _]>, update)
        // DELETE /widgets/:id
        .delete(uri![], delete)
        .collapse();

    Server::bind(&([127, 0, 0, 1], 8080).into())
        .serve(app.into_make_service())
        .await
}

#[derive(Clone, Default)]
struct Db(Arc<Mutex<Store>>);

#[derive(Default)]
struct Store {
    id_gen: u64,
    entries: BTreeMap<u64, Widget>,
}

impl Store {
    fn gen_id(&mut self) -> u64 {
        self.id_gen += 1;
        self.id_gen
    }
}

#[derive(Serialize)]
struct Widget {
    id: u64,
    name: String,
    desc: String,
    count: u32,
}

fn missing_widget(id: u64) -> Response {
    reply::jsonr(&r![error = format!("could not find widget {}", id)])
        .with_status(StatusCode::NOT_FOUND)
}

#[record_args]
async fn new(db: Db, name: String, desc: String, count: u32) -> Response {
    let mut db = db.0.lock().await;

    let id = db.gen_id();

    let entry = db.entries.entry(id).or_insert(Widget {
        id,
        name,
        desc,
        count,
    });

    reply::json(entry).with_status(StatusCode::CREATED)
}

#[record_args]
async fn list(db: Db, range: IdRange) -> Response {
    let db = db.0.lock().await;

    let widgets: Vec<_> = db.entries.range(range).map(|kv| kv.1).collect();

    reply::jsonr(&r![widgets = widgets])
}

#[record_args]
async fn get(db: Db, id: u64) -> Response {
    match db.0.lock().await.entries.get(&id) {
        Some(widget) => reply::json(widget),
        None => missing_widget(id),
    }
}

#[record_args]
async fn update(
    db: Db,
    id: u64,
    name: Option<String>,
    desc: Option<String>,
    count: Option<u32>,
) -> Response
{
    match db.0.lock().await.entries.get_mut(&id) {
        Some(widget) => {
            name.map(|name| widget.name = name);
            desc.map(|desc| widget.desc = desc);
            count.map(|count| widget.count = count);

            reply::json(widget)
        }

        None => missing_widget(id),
    }
}

#[record_args]
async fn delete(db: Db, id: u64) -> Response {
    match db.0.lock().await.entries.remove(&id) {
        Some(widget) => reply::json(&widget),
        None => missing_widget(id),
    }
}
