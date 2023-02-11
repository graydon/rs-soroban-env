use crate::{
    declare_tag_based_wrapper, impl_wrapper_as_and_to_rawval, impl_wrapper_tryfroms_and_tryfromvals,
    impl_wrapper_wasmi_conversions, require, ConversionError, RawVal, RawValConvertible, Tag, TryFromVal, Env, TryIntoVal,
};
use core::{
    cmp::Ordering,
    fmt::Debug,
    hash::{Hash, Hasher},
    str,
};

declare_tag_based_wrapper!(SymbolSmall);
declare_tag_based_wrapper!(SymbolObject);

/// Errors related to operations on the [SymbolObject] and [SymbolSmall] types.
#[derive(Debug)]
pub enum SymbolError {
    /// Returned when attempting to form a [SymbolSmall] from a string with more
    /// than 9 characters.
    TooLong(usize),
    /// Returned when attempting to form a [SymbolObject] or [SymbolSmall] from
    /// a string with characters outside the range `[a-zA-Z0-9_]`.
    BadChar(char),
}

impl core::fmt::Display for SymbolError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SymbolError::TooLong(len) => f.write_fmt(format_args!(
                "symbol too long: length {}, max {}",
                len, MAX_SMALL_CHARS
            )),
            SymbolError::BadChar(char) => f.write_fmt(format_args!(
                "symbol bad char: encountered {}, supported range [a-zA-Z0-9_]",
                char
            )),
        }
    }
}

impl From<SymbolError> for ConversionError {
    fn from(_: SymbolError) -> Self {
        ConversionError
    }
}

extern crate static_assertions as sa;

use super::raw_val::BODY_BITS;

// Small symbols admit 9 6-bit chars for 54 bits.

pub(crate) const MAX_SMALL_CHARS: usize = 9;
const CODE_BITS: usize = 6;
const CODE_MASK: u64 = (1u64 << CODE_BITS) - 1;
sa::const_assert!(CODE_MASK == 0x3f);
sa::const_assert!(CODE_BITS * MAX_SMALL_CHARS + 2 == BODY_BITS);

/// [Symbol] is a static type that asserts that its contained [RawVal] is tagged
/// as either [Tag::SymbolObject] or [Tag::SymbolSmall], and therefore contains
/// a string drawn strictly from the characters `a-zA-Z0-9_`. If this string is
/// 9 or fewer characters long, it will be [SymbolSmall].
#[derive(Copy, Clone)]
pub struct Symbol(RawVal);

impl_wrapper_as_and_to_rawval!(Symbol);
impl_wrapper_tryfroms_and_tryfromvals!(Symbol);
impl_wrapper_wasmi_conversions!(Symbol);

impl<'a, E:Env> TryFromVal<E,SymbolStr<'a>> for Symbol {
    type Error = ConversionError;

    fn try_from_val(env: &E, v: &SymbolStr<'a>) -> Result<Self, Self::Error> {
        if let Ok(ss) = SymbolSmall::try_from_str(v.0) {
            Ok(Self(ss.0))
        }
        else if let Ok(so) = env.symbol_new_from_slice(*v) {
            Ok(Self(so.0))
        } else {
            Err(ConversionError)
        }
    }
}

impl<'a, E:Env> TryFromVal<E,&'a str> for Symbol {
    type Error = ConversionError;

    fn try_from_val(env: &E, v: &&'a str) -> Result<Self, Self::Error> {
        let ss = SymbolStr::try_from_str(v).map_err(|_| ConversionError)?;
        ss.try_into_val(env)
    }

}

impl Symbol {
    pub fn try_from_static<E:Env>(env: &E, v: SymbolStr<'static>) -> Result<Self, ConversionError> {
        if let Ok(ss) = SymbolSmall::try_from_str(v.0) {
            Ok(Self(ss.0))
        }
        else if let Ok(so) = env.symbol_new_from_static_slice(v) {
            Ok(Self(so.0))
        } else {
            Err(ConversionError)
        }
    }

    pub fn try_from_static_str<E:Env>(env: &E, s: &'static str) -> Result<Self, ConversionError> {
        if let Ok(ss) = SymbolStr::try_from_str(s) {
            Self::try_from_static(env, ss)
        } else {
            Err(ConversionError)
        }
    }

    pub const fn try_from_small_str(s: &str) -> Result<Self, SymbolError> {
        match SymbolSmall::try_from_str(s) {
            Ok(ss) => Ok(Symbol(ss.0)),
            Err(e) => Err(e)
        }
    }

    // This should not be generally available as it can easily panic.
    #[cfg(feature = "testutils")]
    pub const fn from_small_str(s: &str) -> Self {
        Symbol(SymbolSmall::from_str(s).0)
    }
}

impl RawValConvertible for Symbol {
    fn is_val_type(v: RawVal) -> bool {
        v.has_tag(Tag::SymbolSmall) || v.has_tag(Tag::SymbolObject)
    }

    unsafe fn unchecked_from_val(v: RawVal) -> Self {
        Self(v)
    }
}

impl From<SymbolSmall> for Symbol {
    fn from(value: SymbolSmall) -> Self {
        unsafe { Self(value.0) }
    }
}

impl From<SymbolObject> for Symbol {
    fn from(value: SymbolObject) -> Self {
        unsafe { Self(value.0) }
    }
}

impl Hash for SymbolSmall {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_raw().get_payload().hash(state);
    }
}

impl PartialEq for SymbolSmall {
    fn eq(&self, other: &Self) -> bool {
        self.as_raw().get_payload() == other.as_raw().get_payload()
    }
}

impl Eq for SymbolSmall {}

impl PartialOrd for SymbolSmall {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SymbolSmall {
    fn cmp(&self, other: &Self) -> Ordering {
        Iterator::cmp(self.into_iter(), other.into_iter())
    }
}

impl Debug for SymbolSmall {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s: SymbolSmallStr = self.into();
        write!(f, "Symbol(")?;
        for c in s.0.iter() {
            if *c == 0 {
                break;
            }
            write!(f, "{}", unsafe { char::from_u32_unchecked(*c as u32) })?;
        }
        write!(f, ")")
    }
}

impl TryFrom<&[u8]> for SymbolSmall {
    type Error = SymbolError;

    fn try_from(b: &[u8]) -> Result<SymbolSmall, SymbolError> {
        Self::try_from_bytes(b)
    }
}

#[cfg(feature = "std")]
use stellar_xdr::StringM;
#[cfg(feature = "std")]
impl<const N: u32> TryFrom<StringM<N>> for SymbolSmall {
    type Error = SymbolError;

    fn try_from(v: StringM<N>) -> Result<Self, Self::Error> {
        v.as_slice().try_into()
    }
}
#[cfg(feature = "std")]
impl<const N: u32> TryFrom<&StringM<N>> for SymbolSmall {
    type Error = SymbolError;

    fn try_from(v: &StringM<N>) -> Result<Self, Self::Error> {
        v.as_slice().try_into()
    }
}

impl SymbolSmall {
    pub const fn try_from_bytes(b: &[u8]) -> Result<SymbolSmall, SymbolError> {
        let mut n = 0;
        let mut accum: u64 = 0;
        while n < b.len() {
            let ch = b[n] as char;
            if n >= MAX_SMALL_CHARS {
                return Err(SymbolError::TooLong(b.len()));
            }
            n += 1;
            accum <<= CODE_BITS;
            let v = match ch {
                '_' => 1,
                '0'..='9' => 2 + ((ch as u64) - ('0' as u64)),
                'A'..='Z' => 12 + ((ch as u64) - ('A' as u64)),
                'a'..='z' => 38 + ((ch as u64) - ('a' as u64)),
                _ => return Err(SymbolError::BadChar(ch)),
            };
            accum |= v;
        }
        Ok(unsafe { Self::from_body(accum) })
    }

    pub const fn try_from_str(s: &str) -> Result<SymbolSmall, SymbolError> {
        Self::try_from_bytes(s.as_bytes())
    }

    // This should not be generally available as it can easily panic.
    #[cfg(feature = "testutils")]
    pub const fn from_str(s: &str) -> SymbolSmall {
        match Self::try_from_str(s) {
            Ok(sym) => sym,
            Err(SymbolError::TooLong(_)) => panic!("symbol too long"),
            Err(SymbolError::BadChar(_)) => panic!("symbol bad char"),
        }
    }

    pub fn to_str(&self) -> SymbolSmallStr {
        let mut chars = [b'\x00'; MAX_SMALL_CHARS];
        for (i, ch) in self.into_iter().enumerate() {
            chars[i] = ch as u8;
        }
        SymbolSmallStr(chars)
    }
}

/// A wrapper around `&str` that checks that the string's
/// characters are in the allowed range. Primarily designed
/// for use with `&'static str`.
#[derive(Copy,Clone,Debug)]
pub struct SymbolStr<'a>(&'a str);
impl<'a> SymbolStr<'a> {

    // We don't use a TryFrom here because we want a const fn.
    const fn try_from_str(ss: &'a str) -> Result<SymbolStr<'a>, SymbolError>
    {
        Self::try_from_bytes(ss.as_bytes())
    }

    const fn try_from_bytes(b: &'a [u8]) -> Result<SymbolStr<'a>, SymbolError>
    {
        let n = b.len();
        let mut i : usize = 0;
        while i < n {
            match b[i] as char {
                '_' |
                '0'..='9' |
                'A'..='Z' |
                'a'..='z' => (),
                x => return Err(SymbolError::BadChar(x))
            }
            i += 1;
        }
        Ok(SymbolStr(unsafe { str::from_utf8_unchecked(b) }))
    }

    pub unsafe fn unchecked_from_bytes(b: &'a [u8]) -> SymbolStr<'a> {
        SymbolStr(unsafe { str::from_utf8_unchecked(b) })
    }

    // This should not be generally available as it can easily panic.
    #[cfg(feature = "testutils")]
    pub const fn from_str(s: &'a str) -> SymbolStr<'a> {
        match Self::try_from_str(s) {
            Ok(sym) => sym,
            Err(SymbolError::TooLong(_)) => panic!("symbol too long"),
            Err(SymbolError::BadChar(_)) => panic!("symbol bad char"),
        }
    }
}

impl<'a> Into<&'a str> for SymbolStr<'a> {
    fn into(self) -> &'a str {
        self.0
    }
}

impl<'a> TryFrom<&'a str> for SymbolStr<'a> {
    type Error = SymbolError;
    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        SymbolStr::try_from_str(value)
    }
}

/// An expanded form of a [SymbolSmall] that stores its characters as
/// ASCII-range bytes in a [u8] array, rather than as packed 6-bit codes within
/// a [u64]. Useful for interoperation with standard Rust string types.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SymbolSmallStr([u8; MAX_SMALL_CHARS]);

impl SymbolSmallStr {
    pub fn is_empty(&self) -> bool {
        self.0[0] == 0
    }
    pub fn len(&self) -> usize {
        let s: &[u8] = &self.0;
        for (i, x) in s.iter().enumerate() {
            if *x == 0 {
                return i;
            }
        }
        s.len()
    }
}

impl Debug for SymbolSmallStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s: &str = self.as_ref();
        f.debug_tuple("SymbolSmallStr").field(&s).finish()
    }
}

impl AsRef<[u8]> for SymbolSmallStr {
    fn as_ref(&self) -> &[u8] {
        let s: &[u8] = &self.0;
        &s[..self.len()]
    }
}

impl AsRef<str> for SymbolSmallStr {
    fn as_ref(&self) -> &str {
        let s: &[u8] = self.as_ref();
        unsafe { str::from_utf8_unchecked(s) }
    }
}

impl From<&SymbolSmall> for SymbolSmallStr {
    fn from(s: &SymbolSmall) -> Self {
        s.to_str()
    }
}

impl From<SymbolSmall> for SymbolSmallStr {
    fn from(s: SymbolSmall) -> Self {
        (&s).into()
    }
}

#[cfg(feature = "std")]
use std::string::{String, ToString};
#[cfg(feature = "std")]
impl From<SymbolSmall> for String {
    fn from(s: SymbolSmall) -> Self {
        s.to_string()
    }
}
#[cfg(feature = "std")]
impl From<SymbolSmallStr> for String {
    fn from(s: SymbolSmallStr) -> Self {
        s.to_string()
    }
}
#[cfg(feature = "std")]
impl ToString for SymbolSmall {
    fn to_string(&self) -> String {
        self.into_iter().collect()
    }
}
#[cfg(feature = "std")]
impl ToString for SymbolSmallStr {
    fn to_string(&self) -> String {
        let s: &str = self.as_ref();
        s.to_string()
    }
}

impl IntoIterator for SymbolSmall {
    type Item = char;
    type IntoIter = SymbolSmallIter;
    fn into_iter(self) -> Self::IntoIter {
        SymbolSmallIter(self.as_raw().get_body())
    }
}

/// An iterator that decodes the individual bit-packed characters from a
/// symbol and yields them as regular Rust [char] values.
#[derive(Clone)]
pub struct SymbolSmallIter(u64);

impl Iterator for SymbolSmallIter {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        while self.0 != 0 {
            let res = match ((self.0 >> ((MAX_SMALL_CHARS - 1) * CODE_BITS)) & CODE_MASK) as u8 {
                1 => b'_',
                n @ (2..=11) => b'0' + n - 2,
                n @ (12..=37) => b'A' + n - 12,
                n @ (38..=63) => b'a' + n - 38,
                _ => b'\0',
            };
            self.0 <<= CODE_BITS;
            if res != b'\0' {
                return Some(res as char);
            }
        }
        None
    }
}

impl FromIterator<char> for SymbolSmall {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut n = 0;
        let mut accum: u64 = 0;
        for i in iter {
            require(n < MAX_SMALL_CHARS);
            n += 1;
            accum <<= CODE_BITS;
            let v = match i {
                '_' => 1,
                '0'..='9' => 2 + ((i as u64) - ('0' as u64)),
                'A'..='Z' => 12 + ((i as u64) - ('A' as u64)),
                'a'..='z' => 38 + ((i as u64) - ('a' as u64)),
                _ => break,
            };
            accum |= v;
        }
        unsafe { Self::from_body(accum) }
    }
}

#[cfg(feature = "std")]
use crate::xdr::ScVal;

#[cfg(feature = "std")]
impl TryFrom<ScVal> for SymbolSmall {
    type Error = ConversionError;
    fn try_from(v: ScVal) -> Result<Self, Self::Error> {
        (&v).try_into()
    }
}
#[cfg(feature = "std")]
impl TryFrom<&ScVal> for SymbolSmall {
    type Error = ConversionError;
    fn try_from(v: &ScVal) -> Result<Self, Self::Error> {
        if let ScVal::Symbol(vec) = v {
            vec.try_into().map_err(|_| ConversionError)
        } else {
            Err(ConversionError)
        }
    }
}

#[cfg(feature = "std")]
impl TryFrom<SymbolSmall> for ScVal {
    type Error = ConversionError;
    fn try_from(s: SymbolSmall) -> Result<Self, Self::Error> {
        let res: Result<Vec<u8>, _> = s.into_iter().map(<u8 as TryFrom<char>>::try_from).collect();
        Ok(ScVal::Symbol(
            res.map_err(|_| ConversionError)?
                .try_into()
                .map_err(|_| ConversionError)?,
        ))
    }
}

#[cfg(feature = "std")]
impl TryFrom<&SymbolSmall> for ScVal {
    type Error = ConversionError;
    fn try_from(s: &SymbolSmall) -> Result<Self, Self::Error> {
        s.clone().try_into()
    }
}

#[cfg(test)]
mod test_without_string {
    use super::{SymbolSmall, SymbolSmallStr};

    #[test]
    fn test_roundtrip() {
        let input = "stellar";
        let sym = SymbolSmall::from_str(input);
        let sym_str = SymbolSmallStr::from(sym);
        let s: &str = sym_str.as_ref();
        assert_eq!(s, input);
    }

    #[test]
    fn test_roundtrip_zero() {
        let input = "";
        let sym = SymbolSmall::from_str(input);
        let sym_str = SymbolSmallStr::from(sym);
        let s: &str = sym_str.as_ref();
        assert_eq!(s, input);
    }

    #[test]
    fn test_roundtrip_nine() {
        let input = "123456789";
        let sym = SymbolSmall::from_str(input);
        let sym_str = SymbolSmallStr::from(sym);
        let s: &str = sym_str.as_ref();
        assert_eq!(s, input);
    }

    #[test]
    fn test_ord() {
        let a_in = "Hello";
        let b_in = "hello";
        let c_in = "hellos";
        let a_sym = SymbolSmall::from_str(a_in);
        let b_sym = SymbolSmall::from_str(b_in);
        let c_sym = SymbolSmall::from_str(c_in);
        assert!(a_sym < b_sym);
        assert!(b_sym < c_sym);
        assert!(a_sym < c_sym);
    }
}

#[cfg(all(test, feature = "std"))]
mod test_with_string {
    use super::SymbolSmall;
    use std::string::{String, ToString};

    #[test]
    fn test_roundtrip() {
        let input = "stellar";
        let sym = SymbolSmall::from_str(input);
        let s: String = sym.to_string();
        assert_eq!(input, &s);
    }

    #[test]
    fn test_roundtrip_zero() {
        let input = "";
        let sym = SymbolSmall::from_str(input);
        let s: String = sym.to_string();
        assert_eq!(input, &s);
    }

    #[test]
    fn test_roundtrip_nine() {
        let input = "123456789";
        let sym = SymbolSmall::from_str(input);
        let s: String = sym.to_string();
        assert_eq!(input, &s);
    }
}
