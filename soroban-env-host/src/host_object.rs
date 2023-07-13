#![allow(dead_code)]

use soroban_env_common::{
    xdr::{ContractCostType, ScErrorCode, ScErrorType},
    Compare, DurationSmall, I128Small, I256Small, I64Small, SymbolSmall, SymbolStr, Tag,
    TimepointSmall, U128Small, U256Small, U64Small,
};

use crate::{
    budget::{AsBudget, Budget},
    host::metered_clone::{self, MeteredClone},
    HostError,
};

use super::{
    host::metered_map::MeteredOrdMap,
    host::metered_vector::MeteredVector,
    num::{I256, U256},
    xdr, AddressObject, BytesObject, DurationObject, Host, I128Object, I256Object, I64Object,
    MapObject, Object, StringObject, SymbolObject, TimepointObject, U128Object, U256Object,
    U64Object, Val, VecObject,
};

pub(crate) type HostMap = MeteredOrdMap<Val, Val, Host>;
pub(crate) type HostVec = MeteredVector<Val>;

#[derive(Clone)]
pub enum HostObject {
    Vec(HostVec),
    Map(HostMap),
    U64(u64),
    I64(i64),
    TimePoint(xdr::TimePoint),
    Duration(xdr::Duration),
    U128(u128),
    I128(i128),
    U256(U256),
    I256(I256),
    Bytes(xdr::ScBytes),
    String(xdr::ScString),
    Symbol(xdr::ScSymbol),
    Address(xdr::ScAddress),
}

impl HostObject {
    // Temporarily performs a shallow comparison against a Val of the
    // associated small value type, returning None if the Val is of
    // the wrong type.
    pub(crate) fn try_compare_to_small(
        &self,
        budget: &Budget,
        rv: Val,
    ) -> Result<Option<core::cmp::Ordering>, HostError> {
        let res = match self {
            HostObject::U64(u) => {
                let Ok(small) = U64Small::try_from(rv) else { return Ok(None) };
                let small: u64 = small.into();
                Some(budget.compare(u, &small)?)
            }
            HostObject::I64(i) => {
                let Ok(small) = I64Small::try_from(rv) else { return Ok(None) };
                let small: i64 = small.into();
                Some(budget.compare(i, &small)?)
            }
            HostObject::TimePoint(tp) => {
                let Ok(small) = TimepointSmall::try_from(rv) else { return Ok(None) };
                let small: u64 = small.into();
                Some(budget.compare(&tp.0, &small)?)
            }
            HostObject::Duration(d) => {
                let Ok(small) = DurationSmall::try_from(rv) else { return Ok(None) };
                let small: u64 = small.into();
                Some(budget.compare(&d.0, &small)?)
            }
            HostObject::U128(u) => {
                let Ok(small) = U128Small::try_from(rv) else { return Ok(None) };
                let small: u128 = small.into();
                Some(budget.compare(u, &small)?)
            }
            HostObject::I128(i) => {
                let Ok(small) = I128Small::try_from(rv) else { return Ok(None) };
                let small: i128 = small.into();
                Some(budget.compare(i, &small)?)
            }
            HostObject::U256(u) => {
                let Ok(small) = U256Small::try_from(rv) else { return Ok(None) };
                let small: U256 = small.into();
                Some(budget.compare(u, &small)?)
            }
            HostObject::I256(i) => {
                let Ok(small) = I256Small::try_from(rv) else { return Ok(None) };
                let small: I256 = small.into();
                Some(budget.compare(i, &small)?)
            }
            HostObject::Symbol(s) => {
                let Ok(small) = SymbolSmall::try_from(rv) else { return Ok(None) };
                let small: SymbolStr = small.into();
                let rhs: &[u8] = small.as_ref();
                Some(budget.compare(&s.as_vec().as_slice(), &rhs)?)
            }

            HostObject::Vec(_)
            | HostObject::Map(_)
            | HostObject::Bytes(_)
            | HostObject::String(_)
            | HostObject::Address(_) => None,
        };
        Ok(res)
    }
}

pub trait HostObjectType: MeteredClone {
    type Wrapper: Into<Object>;
    fn new_from_handle(handle: u32) -> Self::Wrapper;
    fn inject(self) -> HostObject;
    fn try_extract(obj: &HostObject) -> Option<&Self>;
}

// Some host objects are "a slab of memory" which we want
// to treat fairly uniformly in memory-related host functions.
pub(crate) trait MemHostObjectType:
    HostObjectType + TryFrom<Vec<u8>, Error = xdr::Error> + Into<Vec<u8>>
{
    fn as_byte_slice(&self) -> &[u8];
}

macro_rules! declare_host_object_type {
    ($TY:ty, $TAG:ident, $CASE:ident) => {
        impl HostObjectType for $TY {
            type Wrapper = $TAG;
            fn new_from_handle(handle: u32) -> Self::Wrapper {
                unsafe { $TAG::from_handle(handle) }
            }
            fn inject(self) -> HostObject {
                HostObject::$CASE(self)
            }

            fn try_extract(obj: &HostObject) -> Option<&Self> {
                match obj {
                    HostObject::$CASE(v) => Some(v),
                    _ => None,
                }
            }
        }
    };
}

macro_rules! declare_mem_host_object_type {
    ($TY:ty, $TAG:ident, $CASE:ident) => {
        declare_host_object_type!($TY, $TAG, $CASE);
        impl MemHostObjectType for $TY {
            fn as_byte_slice(&self) -> &[u8] {
                self.as_slice()
            }
        }
    };
}

// ${type of contained data}, ${object-wrapper common type}, ${case in HostObject}
declare_host_object_type!(HostMap, MapObject, Map);
declare_host_object_type!(HostVec, VecObject, Vec);
declare_host_object_type!(u64, U64Object, U64);
declare_host_object_type!(i64, I64Object, I64);
declare_host_object_type!(xdr::TimePoint, TimepointObject, TimePoint);
declare_host_object_type!(xdr::Duration, DurationObject, Duration);
declare_host_object_type!(u128, U128Object, U128);
declare_host_object_type!(i128, I128Object, I128);
declare_host_object_type!(U256, U256Object, U256);
declare_host_object_type!(I256, I256Object, I256);
declare_mem_host_object_type!(xdr::ScBytes, BytesObject, Bytes);
declare_mem_host_object_type!(xdr::ScString, StringObject, String);
declare_mem_host_object_type!(xdr::ScSymbol, SymbolObject, Symbol);
declare_host_object_type!(xdr::ScAddress, AddressObject, Address);

// Objects come in two flavors: relative and absolute. Relative objects are the
// ones we pass to and from wasm code, and are looked up indirectly through a
// per-context table to find their absolute values. Absolute objects are the
// same in all contexts (and outside contexts, eg. in host objects themselves or
// while setting-up the host). Relative-to-absolute translation is done very
// close to the VM, when marshalling. Host code should never see relative object
// handles, and if you ever try to look one up in the host object table, it will
// fail.
//
// Also note: the relative/absolute object reference translation is _not_ done
// when running in native / local-testing mode, so you will not get identical
// object numbers in that case. Since there is no real isolation between
// contracts in that mode, there's no point bothering with the translation (and
// there's no really obvious place to perform it systematically, like in the
// wasm marshalling path).

pub fn is_relative_object_handle(handle: u32) -> bool {
    handle & 1 == 0
}

pub fn is_relative_object(obj: Object) -> bool {
    is_relative_object_handle(obj.get_handle())
}

pub fn is_relative_object_value(val: Val) -> bool {
    if let Ok(obj) = Object::try_from(val) {
        is_relative_object(obj)
    } else {
        false
    }
}

pub fn handle_to_index(handle: u32) -> usize {
    (handle as usize) >> 1
}

pub fn index_to_handle(host: &Host, index: usize, relative: bool) -> Result<u32, HostError> {
    if let Ok(smaller) = u32::try_from(index) {
        if let Some(shifted) = smaller.checked_shl(1) {
            if relative {
                return Ok(shifted | 0);
            } else {
                return Ok(shifted | 1);
            }
        }
    }
    Err(host.err_arith_overflow())
}

impl Host {
    /// Moves a value of some type implementing [`HostObjectType`] into the host's
    /// object array, returning a [`HostObj`] containing the new object's array
    /// index, tagged with the [`xdr::ScObjectType`].
    pub(crate) fn add_host_object<HOT: HostObjectType>(
        &self,
        hot: HOT,
    ) -> Result<HOT::Wrapper, HostError> {
        let index = self.try_borrow_objects()?.len();
        let handle = index_to_handle(self, index, false)?;
        // charge for the new host object, which is just the amortized cost of a single
        // `HostObject` allocation
        metered_clone::charge_heap_alloc::<HostObject>(1, self.as_budget())?;
        self.try_borrow_objects_mut()?.push(HOT::inject(hot));
        Ok(HOT::new_from_handle(handle))
    }

    // Notes on metering: closure call needs to be metered separatedly. `VisitObject` only covers
    // the cost of visiting an object.
    pub(crate) unsafe fn unchecked_visit_val_obj<F, U>(
        &self,
        obj: impl Into<Object>,
        f: F,
    ) -> Result<U, HostError>
    where
        F: FnOnce(Option<&HostObject>) -> Result<U, HostError>,
    {
        self.charge_budget(ContractCostType::VisitObject, None)?;
        let r = self.try_borrow_objects()?;
        let obj: Object = obj.into();
        let handle: u32 = obj.get_handle();
        if is_relative_object_handle(handle) {
            Err(self.err(
                ScErrorType::Context,
                ScErrorCode::InternalError,
                "looking up relative object",
                &[obj.to_val()],
            ))
        } else {
            f(r.get(handle_to_index(handle)))
        }
    }

    pub(crate) fn check_val_integrity(&self, val: Val) -> Result<(), HostError> {
        if let Ok(obj) = Object::try_from(val) {
            self.check_obj_integrity(obj)?;
        }
        Ok(())
    }

    pub(crate) fn check_obj_integrity(&self, obj: Object) -> Result<(), HostError> {
        unsafe {
            self.unchecked_visit_val_obj(obj, |hopt| match hopt {
                None => Err(self.err(
                    xdr::ScErrorType::Object,
                    xdr::ScErrorCode::MissingValue,
                    "unknown object reference",
                    &[],
                )),
                Some(hobj) => match (hobj, obj.to_val().get_tag()) {
                    (HostObject::Vec(_), Tag::VecObject)
                    | (HostObject::Map(_), Tag::MapObject)
                    | (HostObject::U64(_), Tag::U64Object)
                    | (HostObject::I64(_), Tag::I64Object)
                    | (HostObject::TimePoint(_), Tag::TimepointObject)
                    | (HostObject::Duration(_), Tag::DurationObject)
                    | (HostObject::U128(_), Tag::U128Object)
                    | (HostObject::I128(_), Tag::I128Object)
                    | (HostObject::U256(_), Tag::U256Object)
                    | (HostObject::I256(_), Tag::I256Object)
                    | (HostObject::Bytes(_), Tag::BytesObject)
                    | (HostObject::String(_), Tag::StringObject)
                    | (HostObject::Symbol(_), Tag::SymbolObject)
                    | (HostObject::Address(_), Tag::AddressObject) => Ok(()),
                    _ => Err(self.err(
                        xdr::ScErrorType::Object,
                        xdr::ScErrorCode::UnexpectedType,
                        "mis-tagged object reference",
                        &[],
                    )),
                },
            })
        }
    }

    // Notes on metering: object visiting part is covered by unchecked_visit_val_obj. Closure function
    // needs to be metered separately.
    pub(crate) fn visit_obj<HOT: HostObjectType, F, U>(
        &self,
        obj: HOT::Wrapper,
        f: F,
    ) -> Result<U, HostError>
    where
        F: FnOnce(&HOT) -> Result<U, HostError>,
    {
        unsafe {
            self.unchecked_visit_val_obj(obj, |hopt| match hopt {
                None => Err(self.err(
                    xdr::ScErrorType::Object,
                    xdr::ScErrorCode::MissingValue,
                    "unknown object reference",
                    &[],
                )),
                Some(hobj) => match HOT::try_extract(hobj) {
                    None => Err(self.err(
                        xdr::ScErrorType::Object,
                        xdr::ScErrorCode::UnexpectedType,
                        "object reference type does not match tag",
                        &[],
                    )),
                    Some(hot) => f(hot),
                },
            })
        }
    }
}
