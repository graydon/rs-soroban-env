#![allow(dead_code)]

use crate::{
    budget::{AsBudget, Budget},
    host::metered_clone,
    num::{I256, U256},
    xdr::{
        self, ContractCostType, LazyScVal, ScErrorCode, ScErrorType, ScMapEntry, ScVal, ScVec,
        ScMap, SCSYMBOL_LIMIT,
    },
    AddressObject, BytesObject, Compare, DurationObject, DurationSmall, Host, HostError,
    I128Object, I128Small, I256Object, I256Small, I64Object, I64Small, MapObject,
    MuxedAddressObject, Object, StringObject, SymbolObject, SymbolSmall, SymbolStr,
    TimepointObject, TimepointSmall, U128Object, U128Small, U256Object, U256Small,
    U64Object, U64Small, Val, VecObject,
};

use core::cmp::Ordering;
use soroban_env_common::Tag;

/// Wrapper for MuxedAccount addresses.
#[derive(Clone, Hash, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct MuxedScAddress(pub(crate) xdr::ScAddress);

/// Convert any typed object wrapper to an untyped Object handle.
pub(crate) fn to_object(v: &impl AsRef<Val>) -> Result<Object, HostError> {
    Object::try_from(*v.as_ref()).map_err(|_| {
        HostError::from((ScErrorType::Object, ScErrorCode::InternalError))
    })
}

// ---------------------------------------------------------------------------
// Object handle utilities
// ---------------------------------------------------------------------------

pub fn is_relative_object_handle(handle: u32) -> bool {
    handle & 1 == 0
}

pub fn handle_to_index(handle: u32) -> usize {
    (handle as usize) >> 1
}

pub fn index_to_handle(host: &Host, index: usize, relative: bool) -> Result<u32, HostError> {
    if let Ok(smaller) = u32::try_from(index) {
        if let Some(shifted) = smaller.checked_shl(1) {
            if relative {
                return Ok(shifted);
            } else {
                return Ok(shifted | 1);
            }
        }
    }
    Err(host.err_arith_overflow())
}

// ---------------------------------------------------------------------------
// Tag from ScValType
// ---------------------------------------------------------------------------

fn tag_from_scval_type(t: xdr::ScValType) -> Option<Tag> {
    use xdr::ScValType;
    match t {
        ScValType::Vec => Some(Tag::VecObject),
        ScValType::Map => Some(Tag::MapObject),
        ScValType::U64 => Some(Tag::U64Object),
        ScValType::I64 => Some(Tag::I64Object),
        ScValType::Timepoint => Some(Tag::TimepointObject),
        ScValType::Duration => Some(Tag::DurationObject),
        ScValType::U128 => Some(Tag::U128Object),
        ScValType::I128 => Some(Tag::I128Object),
        ScValType::U256 => Some(Tag::U256Object),
        ScValType::I256 => Some(Tag::I256Object),
        ScValType::Bytes => Some(Tag::BytesObject),
        ScValType::String => Some(Tag::StringObject),
        ScValType::Symbol => Some(Tag::SymbolObject),
        ScValType::Address => Some(Tag::AddressObject),
        _ => None,
    }
}

fn tag_from_scval(scval: &ScVal) -> Option<Tag> {
    use ScVal::*;
    match scval {
        Vec(_) => Some(Tag::VecObject),
        Map(_) => Some(Tag::MapObject),
        U64(_) => Some(Tag::U64Object),
        I64(_) => Some(Tag::I64Object),
        Timepoint(_) => Some(Tag::TimepointObject),
        Duration(_) => Some(Tag::DurationObject),
        U128(_) => Some(Tag::U128Object),
        I128(_) => Some(Tag::I128Object),
        U256(_) => Some(Tag::U256Object),
        I256(_) => Some(Tag::I256Object),
        Bytes(_) => Some(Tag::BytesObject),
        String(_) => Some(Tag::StringObject),
        Symbol(_) => Some(Tag::SymbolObject),
        Address(_) => Some(Tag::AddressObject),
        _ => None,
    }
}

pub(crate) fn tag_from_lazy_scval(lazy: &LazyScVal) -> Option<Tag> {
    tag_from_scval_type(lazy.discriminant())
}

// ---------------------------------------------------------------------------
// Host object operations — all objects are LazyScVal
// ---------------------------------------------------------------------------

impl Host {
    pub(crate) fn relative_to_absolute(&self, val: Val) -> Result<Val, HostError> {
        if let Ok(obj) = Object::try_from(val) {
            let handle = obj.get_handle();
            return if is_relative_object_handle(handle) {
                let index = handle_to_index(handle);
                let abs_opt = self.with_current_frame_relative_object_table(|table| {
                    Ok(table.get(index).map(|x| *x))
                })?;
                match abs_opt {
                    Some(abs) if abs.to_val().get_tag() == val.get_tag() => Ok(abs.into()),
                    Some(_) => Err(self.err(
                        ScErrorType::Value,
                        ScErrorCode::InvalidInput,
                        "relative and absolute object types differ",
                        &[],
                    )),
                    None => Err(self.err(
                        ScErrorType::Value,
                        ScErrorCode::InvalidInput,
                        "unknown relative object reference",
                        &[Val::from_u32(handle).to_val()],
                    )),
                }
            } else {
                Err(self.err(
                    ScErrorType::Value,
                    ScErrorCode::InvalidInput,
                    "relative_to_absolute given an absolute reference",
                    &[Val::from_u32(handle).to_val()],
                ))
            };
        }
        Ok(val)
    }

    pub(crate) fn absolute_to_relative(&self, val: Val) -> Result<Val, HostError> {
        if let Ok(obj) = Object::try_from(val) {
            let handle = obj.get_handle();
            return if is_relative_object_handle(handle) {
                Err(self.err(
                    ScErrorType::Context,
                    ScErrorCode::InternalError,
                    "absolute_to_relative given a relative reference",
                    &[Val::from_u32(handle).to_val()],
                ))
            } else {
                metered_clone::charge_heap_alloc::<Object>(1, self)?;
                let index = self.with_current_frame_relative_object_table(|table| {
                    let index = table.len();
                    table.push(obj);
                    Ok(index)
                })?;
                let handle = index_to_handle(self, index, true)?;
                Ok(Object::from_handle_and_tag(handle, val.get_tag()).into())
            };
        }
        Ok(val)
    }

    // ----- Core lazy object table operations -----

    /// Get a cloned LazyScVal from the object table. Cheap (Arc clone).
    pub(crate) fn get_lazy_obj(&self, obj: impl AsRef<Val>) -> Result<LazyScVal, HostError> {
        let obj = to_object(&obj)?;
        self.charge_budget(ContractCostType::VisitObject, None)?;
        let handle: u32 = obj.get_handle();
        if is_relative_object_handle(handle) {
            return Err(self.err(
                ScErrorType::Object,
                ScErrorCode::InternalError,
                "looking up relative object",
                &[Val::from_u32(handle).to_val()],
            ));
        }
        let idx = handle_to_index(handle);
        let r = self.try_borrow_objects()?;
        r.get(idx).cloned().ok_or_else(|| {
            self.err(
                ScErrorType::Value,
                ScErrorCode::InvalidInput,
                "unknown object reference",
                &[],
            )
        })
    }

    /// Deserialize a lazy object to ScVal.
    pub(crate) fn deserialize_obj(&self, obj: impl AsRef<Val>) -> Result<ScVal, HostError> {
        let lazy = self.get_lazy_obj(obj)?;
        ScVal::try_from(&lazy).map_err(|_| {
            HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
        })
    }

    /// Add a LazyScVal to the object table, returning a correctly-tagged Object.
    pub(crate) fn add_lazy_obj(&self, lazy: LazyScVal) -> Result<Object, HostError> {
        let _span = tracy_span!("add lazy obj");
        let tag = tag_from_scval_type(lazy.discriminant()).ok_or_else(|| {
            self.err(
                ScErrorType::Value,
                ScErrorCode::InternalError,
                "cannot create object for non-object ScVal type",
                &[],
            )
        })?;
        let index = self.try_borrow_objects()?.len();
        let handle = index_to_handle(self, index, false)?;
        metered_clone::charge_heap_alloc::<LazyScVal>(1, self)?;
        self.try_borrow_objects_mut()?.push(lazy);
        Ok(Object::from_handle_and_tag(handle, tag))
    }

    /// Add an object from a concrete ScVal by serializing to LazyScVal.
    pub(crate) fn add_obj_from_scval(&self, scval: ScVal) -> Result<Object, HostError> {
        let lazy = LazyScVal::try_from(&scval).map_err(|_| {
            HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
        })?;
        self.add_lazy_obj(lazy)
    }

    // ----- Typed convenience methods for adding objects -----

    pub(crate) fn add_obj_u64(&self, v: u64) -> Result<U64Object, HostError> {
        let obj = self.add_obj_from_scval(ScVal::U64(v))?;
        Ok(unsafe { U64Object::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_i64(&self, v: i64) -> Result<I64Object, HostError> {
        let obj = self.add_obj_from_scval(ScVal::I64(v))?;
        Ok(unsafe { I64Object::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_timepoint(&self, v: xdr::TimePoint) -> Result<TimepointObject, HostError> {
        let obj = self.add_obj_from_scval(ScVal::Timepoint(v))?;
        Ok(unsafe { TimepointObject::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_duration(&self, v: xdr::Duration) -> Result<DurationObject, HostError> {
        let obj = self.add_obj_from_scval(ScVal::Duration(v))?;
        Ok(unsafe { DurationObject::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_u128(&self, v: u128) -> Result<U128Object, HostError> {
        let obj = self.add_obj_from_scval(ScVal::U128(xdr::UInt128Parts {
            hi: xdr::int128_helpers::u128_hi(v),
            lo: xdr::int128_helpers::u128_lo(v),
        }))?;
        Ok(unsafe { U128Object::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_i128(&self, v: i128) -> Result<I128Object, HostError> {
        let obj = self.add_obj_from_scval(ScVal::I128(xdr::Int128Parts {
            hi: xdr::int128_helpers::i128_hi(v),
            lo: xdr::int128_helpers::i128_lo(v),
        }))?;
        Ok(unsafe { I128Object::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_u256(&self, v: U256) -> Result<U256Object, HostError> {
        use crate::num::u256_into_pieces;
        let (hi_hi, hi_lo, lo_hi, lo_lo) = u256_into_pieces(v);
        let obj = self.add_obj_from_scval(ScVal::U256(xdr::UInt256Parts {
            hi_hi, hi_lo, lo_hi, lo_lo,
        }))?;
        Ok(unsafe { U256Object::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_i256(&self, v: I256) -> Result<I256Object, HostError> {
        use crate::num::i256_into_pieces;
        let (hi_hi, hi_lo, lo_hi, lo_lo) = i256_into_pieces(v);
        let obj = self.add_obj_from_scval(ScVal::I256(xdr::Int256Parts {
            hi_hi, hi_lo, lo_hi, lo_lo,
        }))?;
        Ok(unsafe { I256Object::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_bytes(&self, v: xdr::ScBytes) -> Result<BytesObject, HostError> {
        let obj = self.add_obj_from_scval(ScVal::Bytes(v))?;
        Ok(unsafe { BytesObject::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_string(&self, v: xdr::ScString) -> Result<StringObject, HostError> {
        let obj = self.add_obj_from_scval(ScVal::String(v))?;
        Ok(unsafe { StringObject::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_symbol(&self, v: xdr::ScSymbol) -> Result<SymbolObject, HostError> {
        let obj = self.add_obj_from_scval(ScVal::Symbol(v))?;
        Ok(unsafe { SymbolObject::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_address(&self, v: xdr::ScAddress) -> Result<AddressObject, HostError> {
        let obj = self.add_obj_from_scval(ScVal::Address(v))?;
        Ok(unsafe { AddressObject::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_muxed_address(&self, v: xdr::ScAddress) -> Result<MuxedAddressObject, HostError> {
        let obj = self.add_obj_from_scval(ScVal::Address(v))?;
        Ok(unsafe { MuxedAddressObject::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_vec_scval(&self, v: ScVec) -> Result<VecObject, HostError> {
        let obj = self.add_obj_from_scval(ScVal::Vec(Some(v)))?;
        Ok(unsafe { VecObject::from_handle(obj.get_handle()) })
    }

    pub(crate) fn add_obj_map_scval(&self, v: ScMap) -> Result<MapObject, HostError> {
        let obj = self.add_obj_from_scval(ScVal::Map(Some(v)))?;
        Ok(unsafe { MapObject::from_handle(obj.get_handle()) })
    }

    /// Validate symbol bytes and add as symbol object.
    pub(crate) fn add_obj_symbol_from_bytes(&self, bytes: Vec<u8>) -> Result<SymbolObject, HostError> {
        if bytes.len() as u64 > SCSYMBOL_LIMIT {
            return Err(self.err(
                ScErrorType::Value,
                ScErrorCode::InvalidInput,
                "slice is too long to be represented as Symbol",
                &[(bytes.len() as u32).into()],
            ));
        }
        for b in &bytes {
            SymbolSmall::validate_byte(*b).map_err(|_| {
                self.err(
                    ScErrorType::Value,
                    ScErrorCode::InvalidInput,
                    "byte is not allowed in Symbol",
                    &[(*b as u32).into()],
                )
            })?;
        }
        let sym = xdr::ScSymbol(bytes.try_into()?);
        self.add_obj_symbol(sym)
    }

    // ----- Vec/Map deserialization helpers -----
    // These deserialize a lazy object to work with its contents.
    // The pattern is: deserialize -> operate -> serialize back.

    /// Deserialize a VecObject to a Vec<ScVal>.
    pub(crate) fn scvec_from_obj(&self, obj: VecObject) -> Result<std::vec::Vec<ScVal>, HostError> {
        let scval = self.deserialize_obj(to_object(&obj)?)?;
        match scval {
            ScVal::Vec(Some(sv)) => Ok(sv.to_vec()),
            ScVal::Vec(None) => Ok(std::vec::Vec::new()),
            _ => Err(HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType))),
        }
    }

    /// Deserialize a MapObject to a Vec<ScMapEntry>.
    pub(crate) fn scmap_from_obj(&self, obj: MapObject) -> Result<std::vec::Vec<ScMapEntry>, HostError> {
        let scval = self.deserialize_obj(to_object(&obj)?)?;
        match scval {
            ScVal::Map(Some(sm)) => Ok(sm.to_vec()),
            ScVal::Map(None) => Ok(std::vec::Vec::new()),
            _ => Err(HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType))),
        }
    }

    /// Binary search for a key in sorted ScMap entries. Returns Ok(idx) if found,
    /// Err(idx) for insertion point.
    pub(crate) fn scmap_find(&self, entries: &[ScMapEntry], key: &ScVal) -> Result<Result<usize, usize>, HostError> {
        let mut lo = 0usize;
        let mut hi = entries.len();
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let cmp = self.as_budget().compare(&entries[mid].key, key)?;
            match cmp {
                Ordering::Less => lo = mid + 1,
                Ordering::Greater => hi = mid,
                Ordering::Equal => return Ok(Ok(mid)),
            }
        }
        Ok(Err(lo))
    }

    // ----- Comparison support for lazy objects -----

    /// Compare a lazy object to a small Val of matching type.
    /// Returns None if types don't match.
    pub(crate) fn lazy_obj_compare_to_small(
        &self,
        lazy: &LazyScVal,
        budget: &Budget,
        rv: Val,
    ) -> Result<Option<Ordering>, HostError> {
        use xdr::ScValType;
        let res = match lazy.discriminant() {
            ScValType::U64 => {
                let Ok(small) = U64Small::try_from(rv) else { return Ok(None) };
                let u = lazy.as_u64().ok_or_else(|| HostError::from((ScErrorType::Value, ScErrorCode::InternalError)))?;
                let small: u64 = small.into();
                Some(budget.compare(&u, &small)?)
            }
            ScValType::I64 => {
                let Ok(small) = I64Small::try_from(rv) else { return Ok(None) };
                let i = lazy.as_i64().ok_or_else(|| HostError::from((ScErrorType::Value, ScErrorCode::InternalError)))?;
                let small: i64 = small.into();
                Some(budget.compare(&i, &small)?)
            }
            ScValType::Timepoint => {
                let Ok(small) = TimepointSmall::try_from(rv) else { return Ok(None) };
                let tp = lazy.as_timepoint().ok_or_else(|| HostError::from((ScErrorType::Value, ScErrorCode::InternalError)))?;
                let small: u64 = small.into();
                Some(budget.compare(&*tp, &small)?)
            }
            ScValType::Duration => {
                let Ok(small) = DurationSmall::try_from(rv) else { return Ok(None) };
                let d = lazy.as_duration().ok_or_else(|| HostError::from((ScErrorType::Value, ScErrorCode::InternalError)))?;
                let small: u64 = small.into();
                Some(budget.compare(&*d, &small)?)
            }
            ScValType::U128 => {
                let Ok(small) = U128Small::try_from(rv) else { return Ok(None) };
                let u = lazy.as_u128().ok_or_else(|| HostError::from((ScErrorType::Value, ScErrorCode::InternalError)))?;
                let val = xdr::int128_helpers::u128_from_pieces(u.hi(), u.lo());
                let small: u128 = small.into();
                Some(budget.compare(&val, &small)?)
            }
            ScValType::I128 => {
                let Ok(small) = I128Small::try_from(rv) else { return Ok(None) };
                let i = lazy.as_i128().ok_or_else(|| HostError::from((ScErrorType::Value, ScErrorCode::InternalError)))?;
                let val = xdr::int128_helpers::i128_from_pieces(i.hi(), i.lo());
                let small: i128 = small.into();
                Some(budget.compare(&val, &small)?)
            }
            ScValType::U256 => {
                let Ok(small) = U256Small::try_from(rv) else { return Ok(None) };
                let u = lazy.as_u256().ok_or_else(|| HostError::from((ScErrorType::Value, ScErrorCode::InternalError)))?;
                let val = crate::num::u256_from_pieces(u.hi_hi(), u.hi_lo(), u.lo_hi(), u.lo_lo());
                let small: U256 = small.into();
                Some(budget.compare(&val, &small)?)
            }
            ScValType::I256 => {
                let Ok(small) = I256Small::try_from(rv) else { return Ok(None) };
                let i = lazy.as_i256().ok_or_else(|| HostError::from((ScErrorType::Value, ScErrorCode::InternalError)))?;
                let val = crate::num::i256_from_pieces(i.hi_hi(), i.hi_lo(), i.lo_hi(), i.lo_lo());
                let small: I256 = small.into();
                Some(budget.compare(&val, &small)?)
            }
            ScValType::Symbol => {
                let Ok(small) = SymbolSmall::try_from(rv) else { return Ok(None) };
                let s = lazy.as_symbol().ok_or_else(|| HostError::from((ScErrorType::Value, ScErrorCode::InternalError)))?;
                let small_str: SymbolStr = small.into();
                let rhs: &[u8] = small_str.as_ref();
                Some(budget.compare(&s.as_bytes(), &rhs)?)
            }
            _ => None,
        };
        Ok(res)
    }
}
