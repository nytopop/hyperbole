//! Compressing dynamic route trie based on [httprouter].
//!
//! [httprouter]: https://github.com/julienschmidt/httprouter
use super::{combinators::Add2, reply::Reply, Response};
use frunk_core::{
    hlist::{HCons, HList, HNil},
    Hlist,
};
use hyper::{
    header::{CONTENT_TYPE, X_CONTENT_TYPE_OPTIONS},
    StatusCode,
};
use std::{cmp, convert::Infallible, fmt, marker::PhantomData, mem, ops::Add, str::FromStr};

/// Expands to a well-typed path specification.
///
/// # Routable segments
/// A [path!] invocation may contain any number of static or dynamic segments separated by
/// forward slashes. Static segments are literal strings and must be matched verbatim when a
/// request comes in, while dynamic segments will match regardless of their content and are
/// *parsed* (via a [FromStr][fromstr] impl) after a route has been matched.
///
/// Parsing errors of dynamic segments will short-circuit a request, responding with an error
/// determined by the [FromStr::Err][std::str::FromStr::Err] (which must implement [Reply]).
///
/// ```
/// use hyperbole::path;
///
/// // /
/// path![];
///
/// // /one
/// path!["one"];
/// // /two
/// path!["one" / "two"];
///
/// // /:one
/// path![one: u32];
/// // /:one/:two
/// path![one: u32 / two: f64];
///
/// // /one/:two/three
/// path!["one" / two: String / "three"];
/// ```
///
/// A catch-all segment may optionally be added to the end of a [path!] to match the rest of
/// an incoming request's path with the same syntax as a dynamic segment, except preceded by
/// a `*`. Like dynamic segments, a name and type must be specified, where the type implements
/// [FromStr][fromstr].
///
/// ```
/// use hyperbole::path;
///
/// // /*any
/// path![*any: String];
///
/// // /one/*everything_else
/// path!["one" / *everything_else: String];
/// ```
///
/// Within an [App], routes must be uniquely determinable. That is, for any request, exactly
/// one or zero routes will match, *always*. Ambiguous routes are not permitted.
///
/// # Query parameters
/// Query parameters may be added to the end of a [path!], but do not affect routing. They are
/// similar to dynamic segments in that they are parsed by a [FromStr][fromstr] impl after a
/// request is matches a route.
///
/// They may be specified as a comma separated list of `name: type` pairs preceded by a `?`
/// after all static, dynamic, and catch-all segments. The order of query parameters does not
/// matter, but duplicates are not permitted.
///
/// If a specified query parameter is not present in a request uri that otherwise matches the
/// path specification, the [FromStr] impl will receive an empty string `""` during parsing.
///
/// ```
/// use hyperbole::path;
///
/// path![? p1: u8];
/// path!["abc" ? p1: u8, p2: String];
/// path!["one" / two: u32 / *three: String ? param: usize, another: f64];
/// ```
///
/// # Interaction with request scoped state
/// Any parameters in a [path!] invocation are tracked as [named fields][field::Field] in a
/// [record!].
///
/// After parsing completes, said record will be merged with any other request scoped state.
///
/// ```
/// use hyperbole::{access, path, record};
///
/// let spec = path!["abc" / num: u32 / *rest: String ? p1: u8, p2: f64];
///
/// let parsed: record![num, rest, p1, p2] = spec
///     // parse_params is called after an App handler matches a route
///     .parse_params("/abc/256/some-more/stuff", Some("p1=40&p2=3.14159"))
///     .unwrap();
///
/// assert_eq!(256, *access!(&parsed.num));
/// assert_eq!("some-more/stuff", *access!(&parsed.rest));
/// assert_eq!(40, *access!(&parsed.p1));
/// assert_eq!(3.14159, *access!(&parsed.p2));
/// ```
///
/// [fromstr]: std::str::FromStr
#[macro_export]
macro_rules! path {
    ($( $token:tt )*) => {
        $crate::__path_internal![
            [$crate::tree::PathSpec::ROOT]
            $( $token )*
        ]
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __path_internal {
    ([$spec:expr]) => {
        $spec
    };

    // at least 1 query param
    ([$spec:expr] ? $( $q_name:ident : $q_type:ty ),+) => {
        ($spec)$( .query::<$crate::f![$q_name : $q_type]>(stringify!($q_name)) )+
    };

    // 1 static seg
    ([$spec:expr] $segment:literal) => {{
        ($spec).segment($segment)
    }};

    // 1 static seg and at least 1 segment
    ([$spec:expr] $segment:literal / $( $token:tt )+) => {
        $crate::__path_internal![
            [($spec).segment($segment)]
            $( $token )+
        ]
    };

    // 1 static seg and at least 1 query param
    ([$spec:expr] $segment:literal ? $( $q_name:ident : $q_type:ty ),+) => {
        $crate::__path_internal![
            [($spec).segment($segment)]
            ? $( $q_name : $q_type ),+
        ]
    };

    // 1 dynamic seg
    ([$spec:expr] $name:ident : $type:ty) => {
        ($spec).dynamic::<$crate::f![$name : $type]>(stringify!($name))
    };

    // 1 dynamic seg and at least 1 segment
    ([$spec:expr] $name:ident : $type:tt / $( $token:tt )+) => {
        $crate::__path_internal![
            [($spec).dynamic::<$crate::f![$name : $type]>(stringify!($name))]
            $( $token )+
        ]
    };

    // 1 dynamic seg and at least 1 query param
    ([$spec:expr] $name:ident : $type:tt ? $( $q_name:ident : $q_type:ty ),+) => {
        $crate::__path_internal![
            [($spec).dynamic::<$crate::f![$name : $type]>(stringify!($name))]
            ? $( $q_name : $q_type ),+
        ]
    };

    // 1 catch-all
    ([$spec:expr] *$name:ident : $type:ty) => {
        ($spec).catch_all::<$crate::f![$name : $type]>(stringify!($name))
    };

    // 1 catch-all and at least 1 segment
    ([$spec:expr] *$name:ident : $type:tt / $( $token:tt )+) => {
        compile_error!(stringify!(
            catch all [*$name: $type] is not the last segment
        ));
    };

    // 1 catch-all and at least 1 query param
    ([$spec:expr] *$name:ident : $type:tt ? $( $q_name:ident : $q_type:ty ),+) => {
        $crate::__path_internal![
            [($spec).catch_all::<$crate::f![$name : $type]>(stringify!($name))]
            ? $( $q_name : $q_type ),+
        ]
    };
}

#[doc(hidden)]
pub trait Parser: Sized {
    type Error: Reply;

    fn parse<'a, I: Iterator<Item = &'a str>>(input: &mut I) -> Result<Self, Self::Error>;
}

impl Parser for HNil {
    type Error = Infallible;

    #[inline]
    fn parse<'a, I: Iterator<Item = &'a str>>(input: &mut I) -> Result<Self, Self::Error> {
        assert! { input.next().is_none() };
        Ok(HNil)
    }
}

// TODO: should input strings be uridecoded first?
impl<T: FromStr, P: HList + Parser> Parser for HCons<T, P>
where T::Err: Reply
{
    // TODO: UriParseError: get rid of URI_MANGLE, it's an inflexible jank
    type Error = Response;

    fn parse<'a, I: Iterator<Item = &'a str>>(input: &mut I) -> Result<Self, Self::Error> {
        let item = input
            .next()
            .expect("parse is always called with exactly the right number of params");

        let head = (item.parse::<T>()).map_err(|e| {
            if <T::Err as Reply>::URI_MANGLE.0 {
                hyper::Response::builder()
                    .status(StatusCode::BAD_REQUEST)
                    .header(CONTENT_TYPE, "text/plain; charset=utf-8")
                    .header(X_CONTENT_TYPE_OPTIONS, "nosniff")
                    .body(format!("failed to parse {:?} in uri", item).into())
                    .unwrap()
            } else {
                e.into_response()
            }
        })?;

        Ok(HCons {
            head,
            tail: P::parse(input).map_err(Reply::into_response)?,
        })
    }
}

#[derive(Copy, Clone)]
struct UriSeg {
    name: &'static str,
    kind: Kind,
}

impl UriSeg {
    const fn new(name: &'static str, kind: Kind) -> Self {
        Self { name, kind }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Kind {
    Static,
    Dynamic,
    CatchAll,
    Query,
}

/// A uri specification and well-typed parameter parser.
///
/// See the [path!] macro for usage details.
pub struct PathSpec<P> {
    segs: Vec<UriSeg>,
    tag: PhantomData<fn(P)>,
}

impl<P> Clone for PathSpec<P> {
    fn clone(&self) -> Self {
        Self::from_segs(self.segs.clone())
    }
}

impl<P> fmt::Display for PathSpec<P> {
    /// ```
    /// use hyperbole::path;
    /// use std::fmt::Display;
    ///
    /// fn eq<D: Display>(a: &str, b: D) {
    ///     assert_eq!(a, format!("{}", b));
    /// }
    ///
    /// eq("/", path![]);
    /// eq("/", path![? p1: u8]);
    /// eq("/one/:two/three", path!["one" / two: u32 / "three"]);
    /// eq("/one/:two/three", path!["one" / two: u32 / "three" ? p1: u8]);
    /// eq("/one/:two/*three", path!["one" / two: u32 / *three: String]);
    /// eq("/one/:two/*three", path!["one" / two: u32 / *three: String ? p1: u8]);
    ///
    /// let a = path!["one" / two: u32 ? p1: u8];
    /// let b = path!["three" / *four: String ? p2: u8];
    /// eq("/one/:two/three/*four", a + b);
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "/")?;

        let mut it = (self.segs.iter())
            .filter(|s| s.kind != Kind::Query)
            .peekable();

        while let Some(UriSeg { name, kind }) = it.next() {
            match kind {
                Kind::Static => write!(f, "{}", name)?,
                Kind::Dynamic => write!(f, ":{}", name)?,
                Kind::CatchAll => write!(f, "*{}", name)?,
                _ => {}
            }

            if it.peek().is_some() {
                write!(f, "/")?;
            }
        }

        Ok(())
    }
}

impl<P: Add<_P>, _P> Add<PathSpec<_P>> for PathSpec<P> {
    type Output = PathSpec<Add2<P, _P>>;

    /// Append a path spec to this path spec.
    ///
    /// # Panics
    /// This panics if `other` is non-empty (except for query parameters) and `self` already
    /// contains a catch-all parameter, or if `other` contains query parameters that already
    /// exist in `self`.
    fn add(mut self, mut other: PathSpec<_P>) -> Self::Output {
        assert! { other.segs.is_empty() || !self.contains_catch_all(),
            "path spec: cannot append to spec that already contains a catch-all",
        }
        if let Some(name) = (other.segs.iter())
            .filter(|s| s.kind == Kind::Query)
            .map(|s| s.name)
            .find(|name| self.contains_query(name))
        {
            panic!("path spec: duplicate query param {:?}", name);
        }
        self.segs.append(&mut other.segs);

        PathSpec::from_segs(self.segs)
    }
}

impl PathSpec<HNil> {
    /// The root path, which has no segments.
    pub const ROOT: Self = PathSpec {
        segs: vec![],
        tag: PhantomData,
    };
}

impl<P> PathSpec<P> {
    fn contains_catch_all(&self) -> bool {
        matches!(
            self.segs.last(),
            Some(s) if s.kind == Kind::CatchAll
        )
    }

    fn from_segs(segs: Vec<UriSeg>) -> Self {
        let tag = PhantomData;
        Self { segs, tag }
    }

    /// Append a static segment to this spec.
    ///
    /// # Panics
    /// This panics if the segment contains `/`, or if the path spec already contains a
    /// catch-all parameter.
    pub fn segment(mut self, name: &'static str) -> Self {
        assert! { !name.contains('/'),
            "path spec: static segments cannot contain '/': {:?}",
            name,
        }
        assert! { !self.contains_catch_all(),
            "path spec: cannot specify static segment after a catch-all",
        }
        self.segs.push(UriSeg::new(name, Kind::Static));

        self
    }

    /// Append a dynamic path parameter of type `T` to this spec.
    ///
    /// # Panics
    /// This panics if the path spec already contains a catch-all parameter.
    pub fn dynamic<T: FromStr>(mut self, name: &'static str) -> PathSpec<Add2<P, Hlist![T]>>
    where P: Add<Hlist![T]> {
        assert! { !self.contains_catch_all(),
            "path spec: cannot specify param after a catch-all",
        }
        self.segs.push(UriSeg::new(name, Kind::Dynamic));

        PathSpec::from_segs(self.segs)
    }

    /// Append a catch-all path parameter of type `T` to this spec.
    ///
    /// # Panics
    /// This panics if the path spec already contains a catch-all parameter.
    pub fn catch_all<T: FromStr>(mut self, name: &'static str) -> PathSpec<Add2<P, Hlist![T]>>
    where P: Add<Hlist![T]> {
        assert! { !self.contains_catch_all(),
            "path spec: cannot specify more than one catch-all",
        }
        self.segs.push(UriSeg::new(name, Kind::CatchAll));

        PathSpec::from_segs(self.segs)
    }

    fn contains_query(&self, name: &str) -> bool {
        (self.segs.iter())
            .filter(|s| s.kind == Kind::Query)
            .any(|s| s.name == name)
    }

    /// Add a query parameter of type `T` to this spec.
    ///
    /// # Panics
    /// This panics if the path spec already contains a query parameter with the same `name`.
    pub fn query<T: FromStr>(mut self, name: &'static str) -> PathSpec<Add2<P, Hlist![T]>>
    where P: Add<Hlist![T]> {
        assert! { !self.contains_query(name),
            "path spec: duplicate query param {:?}",
            name,
        }
        self.segs.push(UriSeg::new(name, Kind::Query));

        PathSpec::from_segs(self.segs)
    }
}

impl<P: Parser> PathSpec<P> {
    /// Parse any parameters present in the provided path and query string.
    ///
    /// # Panics
    /// This panics if `path` does not conform to the shape expected by `P`.
    ///
    /// In practice, this is only called in `hyperbole` after a path has matched a route, and
    /// consequently been guaranteed to have the correct shape.
    pub fn parse_params(&self, mut path: &str, query: Option<&str>) -> Result<P, P::Error> {
        let query = query.unwrap_or_default();

        // split off the first leading slash
        assert!(path.starts_with('/'));
        path = &path[1..];

        P::parse(&mut self.segs.iter().filter_map(|s| match s.kind {
            Kind::Static => {
                // consume until the next slash
                path = path.find('/').map(|i| &path[i + 1..]).unwrap_or("");

                // yield nothing; static segments aren't params
                None
            }

            Kind::Dynamic => {
                // consume to the next slash and yield the segment
                let val = (path.find('/').map(|i| {
                    let seg = &path[..i];
                    path = &path[i + 1..];
                    seg
                }))
                // this is the last segment, consume and yield everything
                .unwrap_or_else(|| mem::take(&mut path));

                Some(val)
            }

            // it's a catch-all, consume and yield everything
            Kind::CatchAll => Some(mem::take(&mut path)),

            Kind::Query => {
                // linear scan to find a query param with the right name
                let val = (query.split('&').find_map(|kv| match kv.find('=')? {
                    // "key=val": kv
                    // "key": kv[..i]
                    // "val": kv[i+1..]
                    i if kv[..i] == *s.name => Some(&kv[i + 1..]),
                    _ => None,
                }))
                // otherwise just yield an empty string
                .unwrap_or_default();

                Some(val)
            }
        }))
    }
}

#[derive(Clone, Debug)]
pub(super) struct Node<H: ?Sized> {
    path: String,
    indices: String,
    wild_child: bool,
    kind: Segment,
    priority: u32,
    children: Vec<Self>,
    entry: Option<Box<H>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Segment {
    Static,
    Root,
    Param,
    CatchAll,
}

impl<H: ?Sized> Default for Node<H> {
    fn default() -> Self {
        Self {
            path: "".into(),
            indices: "".into(),
            wild_child: false,
            kind: Segment::Static,
            priority: 0,
            children: vec![],
            entry: None,
        }
    }
}

impl<H: ?Sized> Node<H> {
    pub fn insert(&mut self, mut path: &str, entry: Box<H>) {
        self.priority += 1;
        if self.path.is_empty() && self.indices.is_empty() {
            self.insert_child(path, path, entry);
            self.kind = Segment::Root;
            return;
        }

        let full_path = path;
        let mut n = self;
        loop {
            let i = longest_common_prefix(path.as_bytes(), n.path.as_bytes());

            // split edge
            if i < n.path.len() {
                let index = n.path.as_bytes()[i];

                let child = Self {
                    path: n.path.split_off(i),
                    indices: mem::take(&mut n.indices),
                    wild_child: n.wild_child,
                    kind: Segment::Static,
                    priority: n.priority - 1,
                    children: mem::take(&mut n.children),
                    entry: mem::take(&mut n.entry),
                };

                n.children.push(child);
                n.indices.push(index.into());
                n.path = path[..i].into();
                n.wild_child = false;
            }

            // make new node a child of this node
            if i < path.len() {
                path = &path[i..];

                if n.wild_child {
                    n = &mut n.children[0];
                    n.priority += 1;

                    if n.wild_child_doesnt_conflict(path) {
                        continue;
                    }

                    let path_seg = match n.kind {
                        Segment::CatchAll => path.splitn(2, '/').next().unwrap(),
                        _ => path,
                    };
                    let idx = full_path.find(path_seg).unwrap();
                    let prefix = format!("{}{}", &full_path[..idx], n.path);

                    panic!(
                        "{:?} in new path {:?} conflicts with existing wildcard {:?} in existing prefix {:?}",
                        path_seg, full_path, n.path, prefix,
                    );
                }

                let idxc = path.as_bytes()[0];

                // '/' after param
                if n.kind == Segment::Param && idxc == b'/' && n.children.len() == 1 {
                    n = &mut n.children[0];
                    n.priority += 1;
                    continue;
                }

                // check if a child with the next path byte exists
                if let Some(i) = n.indices.bytes().position(|c| c == idxc) {
                    n = n.increment_child_prio(i);
                    continue;
                }

                // otherwise, insert it
                if idxc != b':' && idxc != b'*' {
                    n.indices.push(idxc.into());
                    n.children.push(Self::default());
                    n = n.increment_child_prio(n.indices.len() - 1);
                }
                n.insert_child(full_path, path, entry);
                return;
            }

            // otherwise add entry to current node
            assert! { n.entry.replace(entry).is_none(),
                "a handler is already registered for path {:?}",
                full_path,
            }
            return;
        }
    }

    fn wild_child_doesnt_conflict(&self, child: &str) -> bool {
        child.len() >= self.path.len()
            && self.path == child[..self.path.len()]
            && self.kind != Segment::CatchAll
            && (self.path.len() >= child.len() || child.as_bytes()[self.path.len()] == b'/')
    }

    fn increment_child_prio(&mut self, pos: usize) -> &mut Self {
        let cs = &mut self.children;

        cs[pos].priority += 1;
        let prio = cs[pos].priority;

        // adjust position (move to front)
        let mut new_pos = pos;
        while new_pos > 0 && cs[new_pos - 1].priority < prio {
            cs.swap(new_pos, new_pos - 1);
            new_pos -= 1;
        }

        // build new index char string
        if new_pos != pos {
            let idc = &mut self.indices;
            let old = mem::replace(idc, String::with_capacity(idc.len()));

            idc.push_str(&old[..new_pos]); // unchanged prefix, might be empty
            idc.push_str(&old[pos..=pos]); // the index char we moved
            idc.push_str(&old[new_pos..pos]); // everything until char at 'pos'
            idc.push_str(&old[pos + 1..]); // everything after char at 'pos'
        }

        &mut cs[new_pos]
    }

    fn insert_child(&mut self, full_path: &str, mut path: &str, entry: Box<H>) {
        let mut n = self;

        while let Some((mut i, wc, valid)) = find_wildcard(path) {
            assert! { valid,
                "only one wildcard per path segment is permitted, but {:?} was in {:?}",
                wc, full_path,
            }
            assert! { wc.len() >= 2,
                "wildcard {:?} must be named with a non-empty name in path {:?}",
                wc, full_path,
            }
            assert! { n.children.is_empty(),
                "wildcard {:?} conflicts with existing children in path {:?}",
                wc, full_path,
            }

            if wc.as_bytes()[0] == b':' {
                // wc is a :param
                if i > 0 {
                    // insert prefix before the current wildcard
                    n.path = path[..i].into();
                    path = &path[i..];
                }

                n.wild_child = true;
                n.children = vec![Self {
                    path: wc.into(),
                    kind: Segment::Param,
                    priority: 1,
                    ..Self::default()
                }];
                n = &mut n.children[0];

                // if the path doesn't end with the wildcard, there will be another non-wildcard
                // subpath starting with '/'
                if wc.len() < path.len() {
                    path = &path[wc.len()..];
                    n.children = vec![Self::default()];

                    n = &mut n.children[0];
                    n.priority = 1;

                    continue;
                }

                // otherwise we're done; insert the entry into the new leaf
                n.entry = Some(entry);
                return;
            } else {
                // wc is a *catch-all
                assert! { i+wc.len() == path.len(),
                    "catch-all route is not the last segment in path {:?}",
                    full_path,
                }
                assert! { n.path.is_empty() || n.path.as_bytes()[n.path.len()-1] != b'/',
                    "catch-all conflicts with existing entry for path segment root in path {:?}",
                    full_path,
                }
                assert! { path.as_bytes()[i-1] == b'/',
                    "no '/' before catch-all in path {:?}",
                    full_path,
                }

                i -= 1;
                n.path = path[..i].into();
                n.indices = "/".into();

                n.children = vec![Self {
                    wild_child: true,
                    kind: Segment::CatchAll,
                    priority: 1,
                    children: vec![Self {
                        path: path[i..].into(),
                        kind: Segment::CatchAll,
                        priority: 1,
                        entry: Some(entry),
                        ..Self::default()
                    }],
                    ..Self::default()
                }];

                return;
            }
        }

        // if no wildcard was found, just insert entry at path
        n.path = path.into();
        n.entry = Some(entry);
    }

    pub fn lookup(&self, mut path: &str) -> Route<'_, H> {
        let mut r = Route::default();
        let mut n = self;

        loop {
            let prefix = &n.path[..];

            if path.len() > prefix.len() {
                if path[..prefix.len()] == *prefix {
                    path = &path[prefix.len()..];

                    // if this node does not have a wildcard (:param or *catch-all) child, we
                    // can just lookup the next child node and continue walking the tree
                    if !n.wild_child {
                        let idxc = path.as_bytes()[0];

                        if let Some(i) = n.indices.bytes().position(|c| c == idxc) {
                            n = &n.children[i];
                            continue;
                        }

                        // nothing found. we can recommend to redirect to the same URL without
                        // a trailing slash if a leaf exists for that path
                        r.tsr = path == "/" && n.entry.is_some();
                        break r;
                    }

                    n = &n.children[0];

                    if let Segment::Param = n.kind {
                        let end = (path.bytes())
                            .position(|c| c == b'/')
                            .unwrap_or_else(|| path.len());

                        // we must go deeper
                        if end < path.len() {
                            if !n.children.is_empty() {
                                path = &path[end..];
                                n = &n.children[0];
                                continue;
                            }

                            // ... but we can't
                            r.tsr = path.len() == end + 1;
                            break r;
                        }

                        if n.entry.is_some() {
                            r.entry = n.entry.as_deref();
                        } else if n.children.len() == 1 {
                            n = &n.children[0];
                            r.tsr = n.path == "/" && n.entry.is_some();
                        }

                        break r;
                    }

                    if let Segment::CatchAll = n.kind {
                        r.entry = n.entry.as_deref();
                        break r;
                    }

                    panic!("invalid child, expected wildcard but found: {:?}", n.kind);
                }
            } else if path == prefix {
                // we should have reached the node containing the entry, so we check if this
                // node has one registered
                if n.entry.is_some() {
                    r.entry = n.entry.as_deref();
                    break r;
                }

                // if there is no entry for this route, but this route has a wildcard child,
                // there must be an entry for this path with an additional trailing slash
                if path == "/" && n.wild_child && n.kind != Segment::Root {
                    r.tsr = true;
                    break r;
                }

                // no entry found, so check if an entry for the tsr route exists
                if let Some(i) = n.indices.bytes().position(|c| c == b'/') {
                    n = &n.children[i];
                    r.tsr = (n.path.len() == 1 && n.entry.is_some())
                        || (n.kind == Segment::CatchAll && n.children[0].entry.is_some());
                    break r;
                }

                break r;
            }

            // nothing found. we can recommend redirecting to the tsr route if it exists
            r.tsr = path == "/"
                || (prefix.len() == path.len() + 1
                    && prefix.as_bytes()[path.len()] == b'/'
                    && *path == prefix[..prefix.len() - 1]
                    && n.entry.is_some());
            break r;
        }
    }
}

pub(super) struct Route<'a, H: ?Sized> {
    pub entry: Option<&'a H>,
    pub tsr: bool,
}

impl<'a, H: ?Sized> Default for Route<'a, H> {
    fn default() -> Self {
        let entry = None;
        let tsr = false;
        Self { entry, tsr }
    }
}

fn longest_common_prefix(a: &[u8], b: &[u8]) -> usize {
    let mut i = 0;
    let max = cmp::min(a.len(), b.len());
    while i < max && a[i] == b[i] {
        i += 1;
    }
    i
}

fn find_wildcard(path: &str) -> Option<(usize, &str, bool)> {
    // find start index
    for (start, c) in path.bytes().enumerate() {
        // wildcards start with ':' (param) or '*' (catch-all)
        if c != b':' && c != b'*' {
            continue;
        }

        // find end index or invalid chars
        let mut valid = true;
        for (end, c) in path[start + 1..].bytes().enumerate() {
            if c == b':' || c == b'*' {
                valid = false;
            }

            if c == b'/' {
                return Some((start, &path[start..start + 1 + end], valid));
            }
        }

        return Some((start, &path[start..], valid));
    }

    None
}

#[cfg(test)]
mod tests {
    use super::{
        super::{access, path, record},
        *,
    };
    use quickcheck_macros::quickcheck;

    #[test]
    fn test_valid_path_macro_combinations() {
        // only static segments
        path!["one"];
        path!["one" / "two"];

        // only dynamic segments
        path![one: u32];
        path![one: u32 / two: u32];

        // only catch-all segment
        path![*one: String];

        // only query params
        path![? p1: u32];
        path![? p1: u32, p2: u32];

        // static + dynamic segments
        path!["one" / two: u32];
        path![one: u32 / "two"];

        // static + catch-all segments
        path!["one" / *two: String];
        path!["one" / "two" / *three: String];

        // dynamic + catch-all segments
        path![one: u32 / *two: String];
        path![one: u32 / two: u32 / *three: String];

        // static segments + query params
        path!["one" ? p1: u32];
        path!["one" / "two" ? p1: u8, p2: u8];

        // dynamic segments + query params
        path![one: u32 ? p1: u32];
        path![one: u8 / two: u8 ? p1: u8, p2: u8];

        // catch-all segment + query params
        path![*one: String ? p1: u8];
        path![*one: String ? p1: u8, p2:u8];

        // static + dynamic + catch-all segments + query params
        path![one: u32 / "two" / *three: String ? p1: u8];
        path![one: u32 / "two" / *three: String ? p1: u8, p2: u8];
        path!["one" / two: u32 / *three: String ? p1: u8];
        path!["one" / two: u32 / *three: String ? p1: u8, p2: u8];
    }

    #[quickcheck]
    fn test_parse_segments(x: u32) {
        let p = path!["abc" / x: u32 / "cba" / y: String];

        let path = format!("/abc/{}/cba/some-string", x);

        let ps: record![x: u32, y: String] = p.parse_params(&path, None).unwrap();

        assert_eq!(*access!(&ps.x), x);
        assert_eq!(*access!(&ps.y), "some-string");
    }

    #[quickcheck]
    fn test_parse_catch_all(x: u32, rest: String) {
        let p = path!["abc" / x: u32 / *rest: String];

        let path = format!("/abc/{}/{}", x, rest);

        let ps: record![x: u32, rest: String] = p.parse_params(&path, None).unwrap();

        assert_eq!(*access!(&ps.x), x);
        assert_eq!(*access!(&ps.rest), rest);
    }

    #[test]
    fn test_parse_query_params() {
        let p = path![? p1: u8];
        let ps: record![p1: u8] = p.parse_params("/", Some("p1=40")).unwrap();
        assert_eq!(*access!(&ps.p1), 40);

        let p = path![? p1: u32, p2: String];

        let ps: record![p1: u32, p2: String] =
            p.parse_params("/", Some("p1=321&p2=helloworldo")).unwrap();
        assert_eq!(*access!(&ps.p1), 321);
        assert_eq!(*access!(&ps.p2), "helloworldo");

        let ps = p.parse_params("/", Some("p2=helloworldo&p1=300")).unwrap();
        assert_eq!(*access!(&ps.p1), 300);
        assert_eq!(*access!(&ps.p2), "helloworldo");
    }

    #[test]
    fn test_parse_gnarly_appended_mix() {
        let a = path!["one"];
        let b = path![? p1: u8];
        let c = path![two: u32 / "three" ? p2: String];
        let d = path![*four: String ? p3: u8];
        let p = a + b + c + d;

        let ps: record![p1: u8, two: u32, p2: String, four: String, p3: u8] = p
            .parse_params(
                "/one/404/three/and_the/rest/of/it",
                Some("p1=250&p2=hello&p3=4"),
            )
            .unwrap();
        assert_eq!(*access!(&ps.p1), 250);
        assert_eq!(*access!(&ps.p2), "hello");
        assert_eq!(*access!(&ps.p3), 4);
        assert_eq!(*access!(&ps.two), 404);
        assert_eq!(*access!(&ps.four), "and_the/rest/of/it");

        let ps = p
            .parse_params(
                "/one/999999999/three/some/random//string/bro",
                Some("not_a_real_param=gotcha&p3=40&yeet=now&p1=100&fdsa=fortuna"),
            )
            .unwrap();
        assert_eq!(*access!(&ps.p1), 100);
        assert_eq!(*access!(&ps.p2), "");
        assert_eq!(*access!(&ps.p3), 40);
        assert_eq!(*access!(&ps.two), 999999999);
        assert_eq!(*access!(&ps.four), "some/random//string/bro");
    }

    #[test]
    fn test_longest_common_prefix() {
        assert_eq!(0, longest_common_prefix(b"", b""));
        assert_eq!(0, longest_common_prefix(b"", b"a"));
        assert_eq!(0, longest_common_prefix(b"a", b""));

        assert_eq!(0, longest_common_prefix(b"a", b""));
        assert_eq!(0, longest_common_prefix(b"ab", b"ba"));
        assert_eq!(0, longest_common_prefix(b"abc", b"cba"));

        assert_eq!(1, longest_common_prefix(b"a", b"a"));
        assert_eq!(2, longest_common_prefix(b"ab", b"ab"));
        assert_eq!(3, longest_common_prefix(b"abc", b"abc"));

        assert_eq!(3, longest_common_prefix(b"abcxyz", b"abczyx"));
        assert_eq!(3, longest_common_prefix(b"foo", b"foobarbaz"));
        assert_eq!(3, longest_common_prefix(b"foobarbaz", b"foo"));
    }

    #[test]
    fn test_find_wildcard() {
        assert_eq!(None, find_wildcard(""));
        assert_eq!(None, find_wildcard("/"));
        assert_eq!(None, find_wildcard("fdas/"));
        assert_eq!(None, find_wildcard("/fdas"));

        assert_eq!(Some((0, ":ok", true)), find_wildcard(":ok"));
        assert_eq!(Some((1, ":ok", true)), find_wildcard("/:ok"));
        assert_eq!(Some((1, ":ok", true)), find_wildcard("/:ok/:more"));
        assert_eq!(Some((1, ":ok", true)), find_wildcard("/:ok/*more"));

        assert_eq!(Some((0, "*ok", true)), find_wildcard("*ok"));
        assert_eq!(Some((1, "*ok", true)), find_wildcard("/*ok"));
        assert_eq!(Some((1, "*ok", true)), find_wildcard("/*ok/*more"));
        assert_eq!(Some((1, "*ok", true)), find_wildcard("/*ok/:more"));

        assert_eq!(Some((1, ":ok:more", false)), find_wildcard("/:ok:more"));
        assert_eq!(Some((1, ":ok*more", false)), find_wildcard("/:ok*more"));
        assert_eq!(Some((1, "*ok*more", false)), find_wildcard("/*ok*more"));
        assert_eq!(Some((1, "*ok:more", false)), find_wildcard("/*ok:more"));
    }
}
