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

/// Access a [named field][field::Field] in an anonymous record.
///
/// # First form: evaluates to a statement that moves a record field into a variable
/// Immutable: `access!(new_variable = my_record.field_name)`
///
/// Mutable: `access!(mut new_variable = my_record.field_name)`
///
/// The result will be a *statement* that extracts a field, binds its value to the specified
/// identifier, and shadows the original record with any remaining fields.
///
/// The new record will be declared as `mut` in all cases.
///
/// ```
/// use hyperbole::{access, record};
///
/// let rec = record![x = 1000, y = "hello world"];
///
/// access!(s = rec.y);
/// assert_eq!(s, "hello world");
///
/// // NOTE: 'rec' is now eqivalent to 'let mut rec = record![x: 1000]'
///
/// access!(n = rec.x);
/// assert_eq!(n, 1000);
///
/// // NOTE: 'rec' is now empty and contains no fields
/// let _: record![] = rec;
/// ```
///
/// # Second form: evaluates to an expression that borrows a field
/// For immutable borrows: `access!(&my_record.field_name)`
///
/// For mutable borrows: `access!(&mut my_record.field_name)`
///
/// ```
/// use hyperbole::{access, record};
///
/// let mut rec = record![x = 1000, y = "hello world"];
///
/// let _: &u64 = access!(&rec.x);
/// let _: &mut u64 = access!(&mut rec.x);
///
/// assert_eq!(1000, *access!(&rec.x));
/// assert_eq!("hello world", *access!(&rec.y));
///
/// *access!(&mut rec.y) = "changed";
/// assert_eq!("changed", *access!(&rec.y));
///
/// // the type and mutability of 'rec' has not changed
/// let _: record![x: u64, y: &str] = rec;
/// ```
#[macro_export]
macro_rules! access {
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

/// Expands to either the type of an anonymous record, or a (~consty) expression that evaluates
/// to an instantiated record.
///
/// A record is simply an hlist that contains [named fields][field::Field].
///
/// That is, `record![a: u32, b: u32]` is shorthand for `Hlist![f![a: u32], f![b: u32]]`, and
/// `record![a = 4, b = 5]` is shorthand for `hlist![f![a = 4], f![b = 5]]`.
///
/// The syntax is equivalent to [f!], but allows for multiple fields of the same form to be
/// provided as a comma separated list.
///
/// ```
/// use hyperbole::{f, record};
///
/// let mut one = record![a = 2, b = 4, c = "hi"];
///
/// // one is Copy because a, b, and c are Copy:
/// let two: record![a, b, c] = one;
///
/// // types may be specified like in f!:
/// let and: record![a: u32, b: i32, c: &str] = one;
///
/// // accessing fields happens exactly like w/ hlists (as records are hlists):
/// let a: &f![a] = one.get();
/// assert_eq!(2, **a);
///
/// let a: &mut f![a] = one.get_mut();
/// **a = 45;
///
/// let a: f![a] = one.pluck().0;
/// assert_eq!(45, *a);
///
/// // records (ie hlists) also impl Into for tuples, which may be easier to use:
/// let (a, b, c) = one.into();
/// assert_eq!(45, *a);
/// assert_eq!(4, *b);
/// assert_eq!("hi", *c);
/// ```
///
/// # Partial records
/// A group of tokens surrounded by brackets (`[ ]`) may be passed after all named fields to
/// specify additional unnamed fields. Everything within said brackets will be appended to the
/// [Hlist!] or [hlist!] invocation unchanged.
///
/// ```
/// use hyperbole::{f, record, Hlist};
///
/// let my_record = record![a = 40, b = "hello", ["world"]];
///
/// let my_record_infer: record![a, b, [&str]] = my_record;
/// let my_record_concr: record![a: u32, b: &str, [&str]] = my_record;
///
/// let my_record_hlist_infer: Hlist![f![a], f![b], &str] = my_record;
/// let my_record_hlist_concr: Hlist![f![a: u32], f![b: &str], &str] = my_record;
/// ```
#[macro_export]
macro_rules! record {
    () => {
        $crate::hlist::HNil
    };

    ($( $name:ident ),+ $(,)?) => {
        $crate::Hlist![$( $crate::f![$name] ),+]
    };

    ($( $name:ident : $type:ty ),+ $(,)?) => {
        $crate::Hlist![$( $crate::f![$name : $type] ),+]
    };

    ($( $name:ident = $val:expr ),+ $(,)?) => {
        $crate::hlist![$( $crate::f![$name = $val] ),+]
    };

    ($( $name:ident ),+ , [ $( $tok:tt )* ]) => {
        $crate::Hlist![$( $crate::f![$name] ),+ , $( $tok )*]
    };

    ($( $name:ident : $type:ty ),+ , [ $( $tok:tt )* ]) => {
        $crate::Hlist![$( $crate::f![$name : $type] ),+ , $( $tok )*]
    };

    ($( $name:ident = $val:expr ),+ , [ $( $tok:tt )* ]) => {
        $crate::hlist![$( $crate::f![$name = $val] ),+ , $( $tok )*]
    };
}

/// Expands to either the type of a [named field][field::Field], or a (~consty) expression that
/// evaluates to an instantiated field.
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
/// This struct is intended to be named and instantiated via the [f!] or [record!] macros.
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

/// Types with an alternate representation that is [Serialize] and [DeserializeOwned].
pub trait IsoEncode {
    /// The representation.
    type Repr: Serialize + DeserializeOwned;

    /// Convert to the representation.
    fn into_repr(self) -> Self::Repr;

    /// Convert from the representation.
    fn from_repr(repr: Self::Repr) -> Self;
}

impl IsoEncode for HNil {
    type Repr = RNil;

    #[inline]
    fn into_repr(self) -> Self::Repr {
        RNil { __: () }
    }

    #[inline]
    fn from_repr(_: Self::Repr) -> Self {
        HNil
    }
}

impl<T: Serialize + DeserializeOwned, Tail: IsoEncode> IsoEncode for HCons<T, Tail> {
    type Repr = RCons<T, Tail::Repr>;

    #[inline]
    fn into_repr(self) -> Self::Repr {
        RCons {
            head: self.head,
            tail: self.tail.into_repr(),
        }
    }

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

    fn iso_de<T: IsoEncode>(input: &str) -> T {
        T::from_repr(serde_json::from_str(input).unwrap())
    }

    fn iso_ser<T: IsoEncode>(input: T) -> String {
        serde_json::to_string(&input.into_repr()).unwrap()
    }

    fn ser_de_ser<T: IsoEncode + Clone + PartialEq + fmt::Debug>(input: T) {
        let encoded = iso_ser(input.clone());
        let decoded: T = iso_de(&encoded);

        assert_eq!(input, decoded);
    }

    fn de_ser_de<T: IsoEncode>(input: &str) {
        let decoded: T = iso_de(input);
        let encoded = iso_ser(decoded);

        assert_eq!(input, encoded);
    }

    #[quickcheck_macros::quickcheck]
    fn serde_iso_roundtrips(x: u32, y: String, z: f32) {
        ser_de_ser(record![x = x, y = y.clone()]);
        ser_de_ser(record![y = y, x = x, z = z]);
        de_ser_de::<record![x: u32, y: String, z: f32]>(r#"{"x":32,"y":"neat","z":4.4}"#);
    }
}
