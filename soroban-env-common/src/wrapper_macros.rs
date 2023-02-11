#[doc(hidden)]
#[macro_export]
macro_rules! impl_wrapper_tag_based_rawvalconvertible {
    ($tagname:ident) => {
        // A RawValConvertible impl for types where the wrapper _has the same
        // name_ as a Tag:: case and being-that-wrapper is identical to
        // having-that-tag.
        impl $crate::RawValConvertible for $tagname {
            #[inline(always)]
            fn is_val_type(v: $crate::RawVal) -> bool {
                v.has_tag($crate::Tag::$tagname)
            }
            #[inline(always)]
            unsafe fn unchecked_from_val(v: $crate::RawVal) -> Self {
                $tagname(v)
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! impl_wrapper_tag_based_constructors {
    ($tagname:ident) => {
        #[allow(dead_code)]
        impl $tagname {
            #[inline(always)]
            pub(crate) const unsafe fn from_body(body: u64) -> $tagname {
                let rv = $crate::RawVal::from_body_and_tag(body, $crate::Tag::$tagname);
                Self(rv)
            }

            #[inline(always)]
            pub(crate) const unsafe fn from_major_minor(major: u32, minor: u32) -> $tagname {
                let rv =
                    $crate::RawVal::from_major_minor_and_tag(major, minor, $crate::Tag::$tagname);
                Self(rv)
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! impl_wrapper_tryfroms_and_tryfromvals {
    ($T:ty) => {
        impl TryFrom<$crate::RawVal> for $T {
            type Error = $crate::ConversionError;
            #[inline(always)]
            fn try_from(v: $crate::RawVal) -> Result<Self, Self::Error> {
                if let Some(c) = <Self as $crate::RawValConvertible>::try_convert(v) {
                    Ok(c)
                } else {
                    Err($crate::ConversionError)
                }
            }
        }
        impl TryFrom<&$crate::RawVal> for $T {
            type Error = $crate::ConversionError;
            #[inline(always)]
            fn try_from(v: &$crate::RawVal) -> Result<Self, Self::Error> {
                if let Some(c) = <Self as $crate::RawValConvertible>::try_convert(*v) {
                    Ok(c)
                } else {
                    Err($crate::ConversionError)
                }
            }
        }
        impl<E: $crate::Env> $crate::TryFromVal<E, $crate::RawVal> for $T {
            type Error = $crate::ConversionError;
            #[inline(always)]
            fn try_from_val(_env: &E, val: &$crate::RawVal) -> Result<Self, Self::Error> {
                Self::try_from(*val)
            }
        }
        impl<E: $crate::Env> $crate::TryFromVal<E, $T> for $crate::RawVal {
            type Error = $crate::ConversionError;
            fn try_from_val(_env: &E, val: &$T) -> Result<Self, Self::Error> {
                Ok((*val).into())
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! impl_wrapper_wasmi_conversions {
    ($wrapper:ty) => {
        // wasmi / VM argument support
        #[cfg(feature = "vm")]
        impl wasmi::core::FromValue for $wrapper {
            fn from_value(val: wasmi::core::Value) -> Option<Self> {
                let maybe: Option<u64> = <u64 as wasmi::core::FromValue>::from_value(val);
                match maybe {
                    Some(u) => {
                        let raw = $crate::RawVal::from_payload(u);
                        if <Self as $crate::RawValConvertible>::is_val_type(raw) {
                            Some(unsafe {
                                <Self as $crate::RawValConvertible>::unchecked_from_val(raw)
                            })
                        } else {
                            None
                        }
                    }
                    None => None,
                }
            }
        }
        #[cfg(feature = "vm")]
        impl From<$wrapper> for wasmi::core::Value {
            fn from(v: $wrapper) -> Self {
                wasmi::core::Value::I64(v.as_raw().get_payload() as i64)
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! impl_wrapper_as_and_to_rawval {
    ($wrapper:ty) => {
        // AsRef / AsMut to RawVal.
        impl AsRef<$crate::RawVal> for $wrapper {
            fn as_ref(&self) -> &$crate::RawVal {
                &self.0
            }
        }
        impl AsMut<$crate::RawVal> for $wrapper {
            fn as_mut(&mut self) -> &mut $crate::RawVal {
                &mut self.0
            }
        }
        // Basic conversion support: wrapper to raw, and try-into helper.
        impl From<$wrapper> for $crate::RawVal {
            fn from(b: $wrapper) -> Self {
                b.0
            }
        }

        // Various inherent helper / disambiguation methods which
        // may or may-not ever get used per-type, so allowed-dead.
        #[allow(dead_code)]
        impl $wrapper {
            pub const fn as_raw(&self) -> &$crate::RawVal {
                &self.0
            }

            pub const fn to_raw(&self) -> $crate::RawVal {
                self.0
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! impl_wrapper_from_other_type {
    ($fromty:ty, $wrapper:ty) => {
        impl From<$fromty> for $wrapper {
            fn from(x: $fromty) -> Self {
                Self(x.into())
            }
        }
        impl<E: Env> $crate::TryFromVal<E, $wrapper> for $fromty {
            type Error = $crate::ConversionError;
            #[inline(always)]
            fn try_from_val(_env: &E, val: &$wrapper) -> Result<Self, Self::Error> {
                Self::try_from((*val).to_raw())
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! declare_tag_based_wrapper {
    ($T:ident) => {
        #[repr(transparent)]
        #[derive(Copy, Clone)]
        pub struct $T($crate::RawVal);

        $crate::impl_wrapper_as_and_to_rawval!($T);
        $crate::impl_wrapper_wasmi_conversions!($T);
        $crate::impl_wrapper_tryfroms_and_tryfromvals!($T);
        $crate::impl_wrapper_tag_based_rawvalconvertible!($T);
        $crate::impl_wrapper_tag_based_constructors!($T);
    };
}
