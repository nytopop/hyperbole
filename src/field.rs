//! Type level fields for fun and profit.
use super::{reply::Reply, Response};
use frunk_core::hlist::{HCons, HNil};
use serde::{
    de::{self, DeserializeOwned},
    ser, Deserialize, Serialize,
};
use std::{
    fmt,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    str::FromStr,
};

/// Access a [named field][Field] in an hlist.
///
/// # First form: evaluates to a statement that moves an hlist field into a variable
/// Immutable: `zoom!(new_variable = my_record.field_name)`
///
/// Mutable: `zoom!(mut new_variable = my_record.field_name)`
///
/// The result will be a *statement* that extracts a field, binds its value to the specified
/// identifier, and shadows the original hlist with any remaining fields.
///
/// The new hlist will be declared as `mut` in all cases.
///
/// ```
/// use hyperbole::{r, zoom, R};
///
/// let rec = r![x = 1000, y = "hello world"];
///
/// zoom!(s = rec.y);
/// assert_eq!(s, "hello world");
///
/// // NOTE: 'rec' is now eqivalent to 'let mut rec = r![x = 1000]'
///
/// zoom!(n = rec.x);
/// assert_eq!(n, 1000);
///
/// // NOTE: 'rec' is now empty and contains no fields
/// let _: R![] = rec;
/// ```
///
/// # Second form: evaluates to an expression that borrows a field
/// For immutable borrows: `zoom!(&my_record.field_name)`
///
/// For mutable borrows: `zoom!(&mut my_record.field_name)`
///
/// ```
/// use hyperbole::{r, zoom, R};
///
/// let mut rec = r![x = 1000, y = "hello world"];
///
/// let _: &u64 = zoom!(&rec.x);
/// let _: &mut u64 = zoom!(&mut rec.x);
///
/// assert_eq!(1000, *zoom!(&rec.x));
/// assert_eq!("hello world", *zoom!(&rec.y));
///
/// *zoom!(&mut rec.y) = "changed";
/// assert_eq!("changed", *zoom!(&rec.y));
///
/// // the type and mutability of 'rec' has not changed
/// let _: R![x: u64, y: &str] = rec;
/// ```
#[macro_export]
macro_rules! zoom {
    ($var:ident = $rec:ident . $field:ident) => {
        #[allow(unused_mut)]
        let (val, mut $rec) = $rec.pluck::<$crate::f![$field], _>();
        let $var = val.into_inner();
    };

    (mut $var:ident = $rec:ident . $field:ident) => {
        #[allow(unused_mut)]
        let (val, mut $rec) = $rec.pluck::<$crate::f![$field], _>();
        let mut $var = val.into_inner();
    };

    (&$rec:ident . $field:ident) => {
        &**($rec.get::<$crate::f![$field], _>())
    };

    (&mut $rec:ident . $field:ident) => {
        &mut **($rec.get_mut::<$crate::f![$field], _>())
    };
}

/// Expands to the type of an hlist that may contain named fields.
///
/// [Named fields][Field] are used to disambiguate elements of the same type, as most logic in this
/// crate depends on types being unique within hlists.
///
/// Any invocation may contain an arbitrary number of comma separated elements of the form `Type`
/// or `name: Type`. Optionally, `...Type` may be added to the end in order to append the elements
/// of another hlist.
///
/// The [r!] macro may be used to instantiate an hlist value.
///
/// # Examples
/// ```
/// use frunk_core::hlist::{HCons, HNil};
/// use hyperbole::{f, R};
/// #
/// # macro_rules! assert_type_eq {
/// #     ($t1:ty, $t2:ty) => {{
/// #         fn check(mut t1: $t1, t2: $t2) {
/// #             t1 = t2;
/// #         }
/// #     }};
/// # }
///
/// type T = R![u16, u32, u64];
/// type _T = HCons<u16, HCons<u32, HCons<u64, HNil>>>;
/// assert_type_eq!(T, _T);
///
/// type U = R![x: u16, y: u32, z: u64];
/// type _U = HCons<f![x: u16], HCons<f![y: u32], HCons<f![z: u64], HNil>>>;
/// assert_type_eq!(U, _U);
///
/// type V = R![u16, x: u32, u64];
/// type _V = HCons<u16, HCons<f![x: u32], HCons<u64, HNil>>>;
/// assert_type_eq!(V, _V);
///
/// type W = R![foo: String, ...T];
/// type _W = HCons<f![foo: String], HCons<u16, HCons<u32, HCons<u64, HNil>>>>;
/// assert_type_eq!(W, _W);
/// ```
#[macro_export]
macro_rules! R {
    () => {
        $crate::frunk_core::hlist::HNil
    };

    ($name:ident : $type:ty) => {
        $crate::frunk_core::hlist::HCons<
            $crate::field::Field::<$type, { stringify!($name) }>,
            $crate::frunk_core::hlist::HNil,
        >
    };

    ($name:ident : $type:ty , $( $tok:tt )*) => {
        $crate::frunk_core::hlist::HCons<
            $crate::field::Field::<$type, { stringify!($name) }>,
            $crate::R![$( $tok )*],
        >
    };

    ($type:ty) => {
        $crate::frunk_core::hlist::HCons<$type, $crate::frunk_core::hlist::HNil>
    };

    ($type:ty , $( $tok:tt )*) => {
        $crate::frunk_core::hlist::HCons<$type, $crate::R![$( $tok )*]>
    };

    (... $tail:ty) => {
        $tail
    }
}

/// Expands to an hlist that may contain named fields.
///
/// [Named fields][Field] are used to disambiguate elements of the same type, as most logic in this
/// crate depends on types being unique within hlists.
///
/// Any invocation may contain an arbitrary number of comma separated elements of the form `expr`
/// or `name = expr`. Optionally, `...expr` may be added to the end in order to append the elements
/// of another hlist.
///
/// The [R!] macro may be used to name the type of the produced hlist.
///
/// # Examples
/// As hlists are effectively singly linked lists at the type level, the simplest way to refer to
/// an individual element is to follow the struct fields directly:
///
/// ```
/// use hyperbole::r;
///
/// let rec = r![1, 2, 3];
///
/// assert_eq!(rec.head, 1);
/// assert_eq!(rec.tail.head, 2);
/// assert_eq!(rec.tail.tail.head, 3);
/// ```
///
/// Alternatively, they can be converted into tuples:
///
/// ```
/// use hyperbole::r;
///
/// let rec = r![1, "foo", "bar".to_owned()];
/// let (a, b, c) = rec.into();
///
/// assert_eq!(a, 1);
/// assert_eq!(b, "foo");
/// assert_eq!(c, "bar");
/// ```
///
/// See [HCons][frunk_core::hlist::HCons] for more advanced usage.
#[macro_export]
macro_rules! r {
    () => {
        $crate::frunk_core::hlist::HNil
    };

    (... $tail:expr) => {
        $tail
    };

    ($name:ident = $value:expr) => {
        $crate::frunk_core::hlist::HCons {
            head: $crate::field::Field::<_, { stringify!($name) }>::new($value),
            tail: $crate::frunk_core::hlist::HNil,
        }
    };

    ($name:ident = $value:expr , $( $tok:tt )*) => {
        $crate::frunk_core::hlist::HCons {
            head: $crate::field::Field::<_, { stringify!($name) }>::new($value),
            tail: $crate::r![$( $tok )*],
        }
    };

    ($value:expr) => {
        $crate::frunk_core::hlist::HCons {
            head: $value,
            tail: $crate::frunk_core::hlist::HNil,
        }
    };

    ($value:expr , $( $tok:tt )*) => {
        $crate::frunk_core::hlist::HCons {
            head: $value,
            tail: $crate::r![$( $tok )*],
        }
    };
}

/// Expands to either the type of a [named field][Field], or a (~consty) expression that evaluates
/// to an instantiated field.
///
/// # First form: evaluates to the type of a named field with an inferred value type
///
/// ```
/// use hyperbole::f;
///
/// let one: f![abc] = 256.into();
/// let two: f![abc] = one;
/// ```
///
/// Named fields with different names have different types, so for example this will not compile:
///
/// ```compile_fail,E0308
/// use hyperbole::f;
///
/// let one: f![abc] = 1234.into();
/// let two: f![bca] = one;
/// ```
///
/// # Second form: evaluates to the type of a named field with a concrete value type
///
/// ```
/// use hyperbole::f;
///
/// let one: f![abc: u32] = 40.into();
/// let two: f![bca: &str] = "hello world".into();
/// ```
///
/// # Third form: evaluates to an instantiated named field
///
/// ```
/// use hyperbole::f;
///
/// let one = f![hello_world = "this string"];
///
/// const TWO: f![xyz: &str] = f![xyz = "is const"];
/// ```
#[macro_export]
macro_rules! f {
    ($name:ident) => {
        $crate::field::Field<_, { stringify!($name) }>
    };

    ($name:ident : $type:ty) => {
        $crate::field::Field<$type, { stringify!($name) }>
    };

    ($name:ident = $val:expr) => {
        $crate::field::Field::<_, { stringify!($name) }>::new($val)
    };
}

/// A named value where the name is lifted to the type level, analagous to a struct field.
///
/// This struct is intended to be named and instantiated via the [f!] or [r!] / [R!] macros.
///
/// For convenience, `Field<T>` implements [Deref] and [DerefMut] for `T`, as well as a number of
/// fundamental traits like [Clone], [Debug], etc. Consider it a smart pointer to a `T`.
///
/// # Examples
/// ```
/// use hyperbole::f;
///
/// let mut field = f![foo = "neat".to_owned()];
///
/// assert_eq!(4, field.len()); // Deref<Target = String>
/// field.push('o'); // DerefMut
/// assert_eq!("neato", format!("{}", field)); // Display
/// assert_eq!(field, field.clone()); // Clone
///
/// assert_eq!("foo", field.name());
/// ```
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Field<T, const NAME: &'static str> {
    inner: T,
}

impl<T, const NAME: &'static str> Field<T, NAME> {
    /// Returns a new field.
    #[inline]
    pub const fn new(inner: T) -> Self {
        Self { inner }
    }

    /// Extracts the field's inner value.
    #[inline]
    pub fn into_inner(self) -> T {
        self.inner
    }

    /// The field's name.
    pub const NAME: &'static str = NAME;

    /// The field's name.
    pub const fn name(&self) -> &'static str {
        Self::NAME
    }
}

impl<T, const NAME: &'static str> From<T> for Field<T, NAME> {
    #[inline]
    fn from(inner: T) -> Self {
        Self::new(inner)
    }
}

impl<T, const NAME: &'static str> Deref for Field<T, NAME> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T, const NAME: &'static str> DerefMut for Field<T, NAME> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T: FromStr, const NAME: &'static str> FromStr for Field<T, NAME> {
    type Err = T::Err;

    #[inline]
    fn from_str(input: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(input.parse()?))
    }
}

impl<T: fmt::Debug, const NAME: &'static str> fmt::Debug for Field<T, NAME> {
    #[inline]
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(w, "{} = {:?}", NAME, self.inner)
    }
}

impl<T: fmt::Display, const NAME: &'static str> fmt::Display for Field<T, NAME> {
    #[inline]
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(w)
    }
}

impl<T: Reply, const NAME: &'static str> Reply for Field<T, NAME> {
    #[inline]
    fn into_response(self) -> Response {
        self.inner.into_response()
    }
}

impl<T: Serialize, const NAME: &'static str> Serialize for Field<T, NAME> {
    fn serialize<S: ser::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use ser::SerializeStruct;

        let mut s = s.serialize_struct("Field", 1)?;
        s.serialize_field(Self::NAME, &self.inner)?;
        s.end()
    }
}

trait Named {
    const NAME: &'static str;
}

impl<T, const NAME: &'static str> Named for Field<T, NAME> {
    const NAME: &'static str = NAME;
}

impl<'de, T: Deserialize<'de>, const NAME: &'static str> Deserialize<'de> for Field<T, NAME> {
    fn deserialize<D: de::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        enum Tag<Up> {
            Good(PhantomData<fn(Up)>),
            Ignore(PhantomData<fn(Up)>),
        }

        struct TagVisitor<Up>(PhantomData<fn(Up)>);

        impl<'de, Up: Named> de::Visitor<'de> for TagVisitor<Up> {
            type Value = Tag<Up>;

            #[inline]
            fn expecting(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(w, "field identifier")
            }

            #[inline]
            fn visit_u64<E: de::Error>(self, val: u64) -> Result<Self::Value, E> {
                if val == 0 {
                    return Ok(Tag::Good(PhantomData));
                }

                Err(de::Error::invalid_value(
                    de::Unexpected::Unsigned(val),
                    &"field index 0 <= i < 1",
                ))
            }

            #[inline]
            fn visit_str<E: de::Error>(self, val: &str) -> Result<Self::Value, E> {
                if val == Up::NAME {
                    Ok(Tag::Good(PhantomData))
                } else {
                    Ok(Tag::Ignore(PhantomData))
                }
            }

            #[inline]
            fn visit_bytes<E: de::Error>(self, val: &[u8]) -> Result<Self::Value, E> {
                if val == Up::NAME.as_bytes() {
                    Ok(Tag::Good(PhantomData))
                } else {
                    Ok(Tag::Ignore(PhantomData))
                }
            }
        }

        impl<'de, Up: Named> Deserialize<'de> for Tag<Up> {
            #[inline]
            fn deserialize<D: de::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
                d.deserialize_identifier(TagVisitor::<Up>(PhantomData))
            }
        }

        struct Visitor<T, const NAME: &'static str>(PhantomData<fn(Field<T, NAME>)>);

        impl<'de, T: Deserialize<'de>, const NAME: &'static str> de::Visitor<'de> for Visitor<T, NAME> {
            type Value = Field<T, NAME>;

            #[inline]
            fn expecting(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(w, "struct Field")
            }

            #[inline]
            fn visit_seq<A: de::SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                let inner = seq
                    .next_element::<T>()?
                    .ok_or_else(|| de::Error::invalid_length(0, &"struct Field with 1 element"))?;

                Ok(Field { inner })
            }

            #[inline]
            fn visit_map<A: de::MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
                let mut inner: Option<T> = None;

                while let Some(tag) = map.next_key::<Tag<Self::Value>>()? {
                    match tag {
                        Tag::Good(_) if inner.is_some() => {
                            return Err(de::Error::duplicate_field(NAME))
                        }

                        Tag::Good(_) => {
                            inner = Some(map.next_value()?);
                        }

                        Tag::Ignore(_) => {
                            map.next_value::<de::IgnoredAny>()?;
                        }
                    }
                }

                let inner = inner.ok_or_else(|| de::Error::missing_field(NAME))?;

                Ok(Field { inner })
            }
        }

        d.deserialize_struct("Field", &[NAME], Visitor::<T, NAME>(PhantomData))
    }
}

#[derive(Copy, Clone, Default, Serialize, Deserialize)]
#[serde(default)]
#[doc(hidden)]
pub struct RNil {
    #[serde(skip)]
    __: (),
}

#[derive(Copy, Clone, Serialize, Deserialize)]
#[doc(hidden)]
pub struct RCons<T, Tail> {
    #[serde(flatten)]
    head: T,
    #[serde(flatten)]
    tail: Tail,
}

/// Types with an alternate representation that is [Serialize].
///
/// For hlists, the serialization format is equivalent to a struct with the same fields:
///
/// ```
/// use hyperbole::{field::IsoEncode, r};
/// use serde::Serialize;
///
/// #[derive(Serialize)]
/// struct MyRequest {
///     a: String,
///     b: u32,
///     c: f32,
/// }
///
/// let my_req = serde_json::to_string(&MyRequest {
///     a: "hello-worldo".into(),
///     b: 32324,
///     c: 345345.34,
/// })
/// .unwrap();
///
/// let my_req_r = serde_json::to_string(
///     &r! {
///         a = "hello-worldo".to_string(),
///         b = 32324,
///         c = 345345.34,
///     }
///     .as_repr(),
/// )
/// .unwrap();
///
/// // both of the above serialize to:
/// let repr = r#"{"a":"hello-worldo","b":32324,"c":345345.34}"#;
///
/// assert_eq!(repr, my_req);
/// assert_eq!(repr, my_req_r);
/// ```
pub trait IsoEncode<'a> {
    /// The representation.
    type Repr: Serialize;

    /// Convert to the representation.
    fn as_repr(&'a self) -> Self::Repr;
}

impl<'a> IsoEncode<'a> for HNil {
    type Repr = RNil;

    #[inline]
    fn as_repr(&'a self) -> Self::Repr {
        RNil { __: () }
    }
}

impl<'a, T: Serialize + 'a, Tail: IsoEncode<'a>> IsoEncode<'a> for HCons<T, Tail> {
    type Repr = RCons<&'a T, Tail::Repr>;

    #[inline]
    fn as_repr(&'a self) -> Self::Repr {
        RCons {
            head: &self.head,
            tail: self.tail.as_repr(),
        }
    }
}

/// Types with an alternate representation that is [DeserializeOwned].
///
/// For hlists, the deserialization format is equivalent to a struct with the same fields:
///
/// ```
/// use hyperbole::{field::IsoDecode, zoom, R};
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct MyRequest {
///     a: String,
///     b: u32,
///     c: f32,
/// }
///
/// let repr = r#"{"a":"hello-worldo","b":32324,"c":345345.34}"#;
///
/// let my_req: MyRequest = serde_json::from_str(repr).unwrap();
///
/// let my_req_r: R![a: String, b: u32, c: f32] = serde_json::from_str(repr)
///     .map(IsoDecode::from_repr)
///     .unwrap();
///
/// assert_eq!(my_req.a, *zoom![&my_req_r.a]);
/// assert_eq!(my_req.b, *zoom![&my_req_r.b]);
/// assert_eq!(my_req.c, *zoom![&my_req_r.c]);
/// ```
pub trait IsoDecode {
    /// The representation.
    type Repr: DeserializeOwned;

    /// Convert from the representation.
    fn from_repr(repr: Self::Repr) -> Self;
}

impl IsoDecode for HNil {
    type Repr = RNil;

    #[inline]
    fn from_repr(_: Self::Repr) -> Self {
        HNil
    }
}

impl<T: DeserializeOwned, Tail: IsoDecode> IsoDecode for HCons<T, Tail> {
    type Repr = RCons<T, Tail::Repr>;

    #[inline]
    fn from_repr(repr: Self::Repr) -> Self {
        HCons {
            head: repr.head,
            tail: Tail::from_repr(repr.tail),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck_macros::quickcheck;

    fn iso_de<T: IsoDecode>(input: &str) -> T {
        T::from_repr(serde_json::from_str(input).unwrap())
    }

    fn iso_ser<'a, T: IsoEncode<'a>>(input: &'a T) -> String {
        serde_json::to_string(&input.as_repr()).unwrap()
    }

    fn ser_de_ser<T: IsoDecode + PartialEq + fmt::Debug>(input: T)
    where T: for<'a> IsoEncode<'a> {
        let encoded = iso_ser(&input);
        let decoded: T = iso_de(&encoded);

        assert_eq!(input, decoded);
    }

    fn de_ser_de<T: IsoDecode>(input: &str)
    where T: for<'a> IsoEncode<'a> {
        let decoded: T = iso_de(input);
        let encoded = iso_ser(&decoded);

        assert_eq!(input, encoded);
    }

    #[quickcheck]
    fn serde_iso_roundtrips(x: u32, y: String, z: f32) {
        ser_de_ser(r![x = x, y = y.clone()]);
        ser_de_ser(r![y = y, x = x, z = z]);
        de_ser_de::<R![x: u32, y: String, z: f32]>(r#"{"x":32,"y":"neat","z":4.4}"#);
    }
}
