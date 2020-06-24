//! Server sent events.
use crate::{field::IsoEncode, reply::Reply, Response};
use bytes::BytesMut;
use futures::{
    ready,
    stream::{Stream, StreamExt},
};
use headers::{CacheControl, ContentType};
use hyper::Body;
use pin_project::pin_project;
use serde::Serialize;
use std::{
    convert::Infallible,
    future::Future,
    pin::Pin,
    task::{Context, Poll},
    time::Duration,
};
use tokio::time::{delay_for, Delay, Instant};

/// A stream of server sent [Event]s.
pub struct EventStream<S> {
    inner: S,
}

impl<S: Stream<Item = Vec<Event>> + Send + 'static> Reply for EventStream<S> {
    fn into_response(self) -> Response {
        let events = self.inner.map(|mut events| {
            let mut buf = BytesMut::new();

            // comments, event names, and data must arrive before identifiers so that
            // the Last-Event-ID has all relevant content fields fully transferred.
            events.sort_by_key(|e| e.tag);
            events.iter().for_each(|e| e.write_buf(&mut buf));

            Ok::<_, Infallible>(buf)
        });

        hyper::Response::builder()
            .body(Body::wrap_stream(events))
            .unwrap()
            .with_header(ContentType::from(mime::TEXT_EVENT_STREAM))
            .with_header(CacheControl::new().with_no_cache())
    }
}

impl<S: Stream<Item = Vec<Event>>> EventStream<S> {
    /// Create an sse stream.
    ///
    /// Events within the same `Vec<Event>` will be reordered using a stable sort.
    ///
    /// # Examples
    /// ```
    /// use futures::stream;
    /// use hyperbole::{
    ///     path,
    ///     reply::sse::{Event, EventStream},
    ///     App, Hlist,
    /// };
    ///
    /// let _app = App::empty()
    ///     .context()
    ///     .get(path!["my-first-event-stream"], |cx: Hlist![]| async {
    ///         let events = stream::iter(Some(vec![
    ///             Event::comment("this is an event"),
    ///             Event::id("neato"),
    ///             Event::data("hello worldo"),
    ///             Event::event("test"),
    ///         ]));
    ///
    ///         EventStream::new(events)
    ///     })
    ///     .collapse();
    /// ```
    pub fn new(events: S) -> Self {
        Self { inner: events }
    }
}

impl<S: Stream<Item = Vec<Event>>> EventStream<Padded<S>> {
    /// Create an sse stream that ensures at least one event is sent every `keepalive`.
    ///
    /// Events within the same `Vec<Event>` will be reordered using a stable sort.
    ///
    /// # Examples
    /// ```
    /// use futures::stream;
    /// use hyperbole::{
    ///     path,
    ///     reply::sse::{Event, EventStream},
    ///     App, Hlist,
    /// };
    /// use std::time::Duration;
    ///
    /// let _app = App::empty()
    ///     .context()
    ///     .get(path!["my-first-event-stream"], |cx: Hlist![]| async {
    ///         let events = stream::iter(Some(vec![
    ///             Event::comment("this is an event"),
    ///             Event::id("neato"),
    ///             Event::data("hello worldo"),
    ///             Event::event("test"),
    ///         ]));
    ///
    ///         EventStream::keepalive(Duration::from_secs(15), events)
    ///     })
    ///     .collapse();
    /// ```
    pub fn keepalive(keepalive: Duration, events: S) -> Self {
        let padded = Padded {
            inner: events,
            interval: keepalive,
            timer: delay_for(keepalive),
            item: vec![Event::comment("")],
        };

        Self { inner: padded }
    }
}

/// A server sent event.
///
/// Events with multiline payloads will serialize as multiple successive events of the same type,
/// one for each line.
#[derive(Debug, Clone)]
pub struct Event {
    payload: String,
    tag: Tag,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Tag {
    Comment = 0,
    Event = 1,
    Data = 2,
    Id = 3,
    Retry = 4,
}

impl Event {
    const fn new(payload: String, tag: Tag) -> Self {
        Self { payload, tag }
    }

    /// Create a new comment event (`:`).
    pub fn comment<P: Into<String>>(payload: P) -> Self {
        Self::new(payload.into(), Tag::Comment)
    }

    /// Create a new event name event (`event:`).
    pub fn event<P: Into<String>>(payload: P) -> Self {
        Self::new(payload.into(), Tag::Event)
    }

    /// Create a new data event.
    pub fn data<P: Into<String>>(payload: P) -> Self {
        Self::new(payload.into(), Tag::Data)
    }

    /// Create a new data event with a json object.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::reply::sse::Event;
    /// use serde::Serialize;
    ///
    /// #[derive(Serialize)]
    /// struct MyEvent<'a> {
    ///     x: u32,
    ///     y: i16,
    ///     z: &'a str,
    /// }
    ///
    /// let _ = Event::json(&MyEvent {
    ///     x: 4,
    ///     y: 5,
    ///     z: "hello world",
    /// });
    /// ```
    pub fn json<T: Serialize>(payload: &T) -> Self {
        Self::new(serde_json::to_string(payload).unwrap(), Tag::Data)
    }

    /// Create a new data event with a json anonymous record.
    ///
    /// # Examples
    /// ```
    /// use hyperbole::{record, reply::sse::Event};
    ///
    /// let _ = Event::jsonr(&record![x = 4, y = 5, z = "hello world"]);
    /// ```
    pub fn jsonr<'a, T: IsoEncode<'a>>(payload: &'a T) -> Self {
        Self::json(&payload.as_repr())
    }

    /// Create a new id event.
    pub fn id<P: Into<String>>(payload: P) -> Self {
        Self::new(payload.into(), Tag::Id)
    }

    /// Create a new retry event.
    pub fn retry(after: Duration) -> Self {
        Self::new(format!("{}", after.as_millis()), Tag::Retry)
    }

    fn write_buf(&self, buf: &mut BytesMut) {
        let tag = match self.tag {
            Tag::Comment => ":",
            Tag::Event => "event:",
            Tag::Data => "data:",
            Tag::Id => "id:",
            Tag::Retry => "retry:",
        };

        for line in self.payload.split('\n') {
            buf.extend_from_slice(tag.as_bytes());
            buf.extend_from_slice(line.as_bytes());
            buf.extend_from_slice("\n".as_bytes());
        }
    }
}

/// A stream that will be padded with a fixed item whenever it is blocked for too long.
#[pin_project]
pub struct Padded<S: Stream> {
    #[pin]
    inner: S,
    interval: Duration,
    timer: Delay,
    item: S::Item,
}

impl<S: Stream> Stream for Padded<S>
where S::Item: Clone
{
    type Item = S::Item;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let mut pin = self.project();

        match pin.inner.poll_next(cx) {
            Poll::Pending => {
                ready!(Pin::new(&mut pin.timer).poll(cx));
                pin.timer.reset(Instant::now() + *pin.interval);
                Poll::Ready(Some(pin.item.clone()))
            }

            Poll::Ready(Some(e)) => {
                pin.timer.reset(Instant::now() + *pin.interval);
                Poll::Ready(Some(e))
            }

            Poll::Ready(None) => Poll::Ready(None),
        }
    }
}
