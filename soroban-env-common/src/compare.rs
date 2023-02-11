#[cfg(feature = "std")]
use std::rc::Rc;

use crate::{Env, Object, RawVal, RawValConvertible, Status, Symbol, Tag};
use core::cmp::Ordering;

/// General trait representing the ability to compare two values of some type.
/// Similar to `core::cmp::Cmp` but with two key differences: the comparison is
/// fallible, and is provided by some external type implementing `Compare`
/// rather than the compared type itself.
///
/// This trait exists to support comparing `RawVal`s with help from the
/// environment in which object handles are defined, and allowing for the
/// possibility of erroneous inputs like invalid object handles, as well as the
/// possibility of running over budget during the comparison. It is also used
/// in other places where comparison work has to be budgeted, such as inside
/// the host's storage maps.
pub trait Compare<T> {
    type Error;
    fn compare(&self, a: &T, b: &T) -> Result<Ordering, Self::Error>;
}

impl<T, C: Compare<T>> Compare<&T> for C {
    type Error = C::Error;

    fn compare(&self, a: &&T, b: &&T) -> Result<Ordering, Self::Error> {
        <C as Compare<T>>::compare(self, *a, *b)
    }
}

impl<T, C: Compare<T>> Compare<Option<T>> for C {
    type Error = C::Error;

    fn compare(&self, a: &Option<T>, b: &Option<T>) -> Result<Ordering, Self::Error> {
        match (a, b) {
            (Some(a), Some(b)) => <C as Compare<T>>::compare(self, a, b),
            (None, None) => Ok(Ordering::Equal),
            (None, Some(_)) => Ok(Ordering::Less),
            (Some(_), None) => Ok(Ordering::Greater),
        }
    }
}

impl<T, U, V, E, C> Compare<(T, U, V)> for C
where
    C: Compare<T, Error = E> + Compare<U, Error = E> + Compare<V, Error = E>,
{
    type Error = E;

    fn compare(&self, a: &(T, U, V), b: &(T, U, V)) -> Result<Ordering, Self::Error> {
        match <C as Compare<T>>::compare(self, &a.0, &b.0)? {
            Ordering::Equal => match <C as Compare<U>>::compare(self, &a.1, &b.1)? {
                Ordering::Equal => <C as Compare<V>>::compare(self, &a.2, &b.2),
                unequal => Ok(unequal),
            },
            unequal => Ok(unequal),
        }
    }
}

impl<T, U, E, C> Compare<(T, U)> for C
where
    C: Compare<T, Error = E> + Compare<U, Error = E>,
{
    type Error = E;

    fn compare(&self, a: &(T, U), b: &(T, U)) -> Result<Ordering, Self::Error> {
        match <C as Compare<T>>::compare(self, &a.0, &b.0)? {
            Ordering::Equal => <C as Compare<U>>::compare(self, &a.1, &b.1),
            unequal => Ok(unequal),
        }
    }
}

#[cfg(feature = "std")]
impl<T, C: Compare<T>> Compare<Vec<T>> for C {
    type Error = C::Error;

    fn compare(&self, a: &Vec<T>, b: &Vec<T>) -> Result<Ordering, Self::Error> {
        let mut i = 0;
        loop {
            match (a.get(i), b.get(i)) {
                (None, None) => return Ok(Ordering::Equal),
                (None, Some(_)) => return Ok(Ordering::Less),
                (Some(_), None) => return Ok(Ordering::Greater),
                (Some(a), Some(b)) => match <C as Compare<T>>::compare(self, a, b)? {
                    Ordering::Equal => i += 1,
                    unequal => return Ok(unequal),
                },
            }
        }
    }
}

#[cfg(feature = "std")]
impl<T, C: Compare<T>> Compare<Box<T>> for C {
    type Error = C::Error;

    fn compare(&self, a: &Box<T>, b: &Box<T>) -> Result<Ordering, Self::Error> {
        <Self as Compare<T>>::compare(self, &*a, &*b)
    }
}

#[cfg(feature = "std")]
impl<T, C: Compare<T>> Compare<Rc<T>> for C {
    type Error = C::Error;

    fn compare(&self, a: &Rc<T>, b: &Rc<T>) -> Result<Ordering, Self::Error> {
        <Self as Compare<T>>::compare(self, &*a, &*b)
    }
}

// Apparently we can't do a blanket T:Ord impl because there are Ord derivations
// that also go through &T and Option<T> that conflict with our impls above
// (patches welcome from someone who understands trait-system workarounds
// better). But we can list out any concrete Ord instances we want to support
// here.

impl<E: Env> Compare<Object> for E {
    type Error = E::Error;

    fn compare(&self, a: &Object, b: &Object) -> Result<Ordering, Self::Error> {
        let v = self.obj_cmp(a.to_raw(), b.to_raw())?;
        if v == 0 {
            Ok(Ordering::Equal)
        } else if v < 0 {
            Ok(Ordering::Less)
        } else {
            Ok(Ordering::Greater)
        }
    }
}

impl<E: Env> Compare<RawVal> for E {
    type Error = E::Error;

    fn compare(&self, a: &RawVal, b: &RawVal) -> Result<Ordering, Self::Error> {
        let a_tag = a.get_tag();
        let b_tag = b.get_tag();
        if a_tag < b_tag {
            Ok(Ordering::Less)
        } else if a_tag > b_tag {
            Ok(Ordering::Greater)
        } else {
            // Tags are equal so we only have to switch on one.
            if a.is_object() {
                // Fast-path equal handles
                if a.get_body() == b.get_body() {
                    return Ok(Ordering::Equal);
                } else {
                    let a = unsafe { Object::unchecked_from_val(*a) };
                    let b = unsafe { Object::unchecked_from_val(*b) };
                    return self.compare(&a, &b);
                }
            }
            match a_tag {
                Tag::False => Ok(Ordering::Equal),
                Tag::True => Ok(Ordering::Equal),
                Tag::Void => Ok(Ordering::Equal),

                Tag::Status => {
                    let a = unsafe { <Status as RawValConvertible>::unchecked_from_val(*a) };
                    let b = unsafe { <Status as RawValConvertible>::unchecked_from_val(*b) };
                    Ok(a.cmp(&b))
                }
                Tag::U32 => {
                    let a = unsafe { <u32 as RawValConvertible>::unchecked_from_val(*a) };
                    let b = unsafe { <u32 as RawValConvertible>::unchecked_from_val(*b) };
                    Ok(a.cmp(&b))
                }
                Tag::I32 => {
                    let a = unsafe { <i32 as RawValConvertible>::unchecked_from_val(*a) };
                    let b = unsafe { <i32 as RawValConvertible>::unchecked_from_val(*b) };
                    Ok(a.cmp(&b))
                }

                Tag::U64Small
                | Tag::TimepointSmall
                | Tag::DurationSmall
                | Tag::U128Small
                | Tag::U256Small => Ok(a.get_body().cmp(&b.get_body())),

                Tag::I64Small | Tag::I128Small | Tag::I256Small => {
                    Ok(a.get_signed_body().cmp(&b.get_signed_body()))
                }

                Tag::SymbolSmall => todo!(),

                Tag::LedgerKeyContractExecutable => Ok(Ordering::Equal),

                Tag::SmallCodeUpperBound => Ok(Ordering::Equal),
                Tag::ObjectCodeLowerBound => Ok(Ordering::Equal),

                // None of the object cases should be reachable, they
                // should all have been handled by the is_object() branch
                // above.
                Tag::U64Object
                | Tag::I64Object
                | Tag::TimepointObject
                | Tag::DurationObject
                | Tag::U128Object
                | Tag::I128Object
                | Tag::U256Object
                | Tag::I256Object
                | Tag::BytesObject
                | Tag::StringObject
                | Tag::SymbolObject
                | Tag::VecObject
                | Tag::MapObject
                | Tag::ContractExecutableObject
                | Tag::AddressObject
                | Tag::LedgerKeyNonceObject => unreachable!(),

                Tag::ObjectCodeUpperBound => Ok(Ordering::Equal),
                Tag::Bad => Ok(Ordering::Equal),
            }
        }
    }
}
