use std::{
    collections::HashMap,
    rc::Rc,
    sync::{Arc, Mutex},
};

use soroban_env_common::SymbolStr;

use crate::{host::metered_map::HostContext, HostError};

use super::{
    host::metered_map::MeteredOrdMap,
    host::metered_vector::MeteredVector,
    num::{I256, U256},
    xdr, Host, RawVal,
};

pub(crate) type HostMap = MeteredOrdMap<RawVal, RawVal, HostContext>;
pub(crate) type HostVec = MeteredVector<RawVal>;

// FIXME: update XDR definition with this wrapper.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub(crate) struct ScNonceKey(xdr::ScAddress);

// Static guest slices are pointers into a _data segment_ of a guest VM's
// (static) module. They do _not_ point into linear memory; the point into the
// pre-image of part of linear memory, an input to it that is stored in the
// module file before linear memory is initialized.
//
//  Here is a typical set of data segment descriptions from a WASM file:
//
// Data[2]:
//  - segment[0] <.rodata> memory=0 size=58389 - init i32=1048576
//  - segment[1] <.data> memory=0 size=16 - init i32=1106968
//
// This is describing some constant data that's going to be copied into linear
// memory when the program starts up. Each is placed at an offset (the i32=...
// expression) in linear memory. These are not _zero_ because linear memory is
// organized as follows (on the LLVM WASM backends):
//
//       .....
//    |          | ^
//    |  heap    | | heap grows up
//    |          | |
//    |          |
//    +----------+ <-- heap begins at data + all data sizes
//    |          |
//    |  data    |
//    |          |
//    +----------+ <-- data begins at 0x100000 (== 1048576 a.k.a 1MiB)
//    |          |
//    |          | |
//    | stack    | | stack grows down
//    |          | V
//    |          |
//    +----------+ 0
//
// When we build a static guest slice, we do so starting from a linear memory
// (offset, length) pair. We _translate_ this to an (offset, length) pair inside
// a specific data segment (if we find one that spans it).

#[cfg(feature = "vm")]
#[derive(Clone, Debug)]
struct StaticGuestSlice {
    module: Arc<wasmi::Module>,
    segment: usize,
    offset: u32,
    length: u32,
}

#[cfg(feature = "vm")]
impl std::hash::Hash for StaticGuestSlice {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.module).hash(state);
        self.segment.hash(state);
        self.offset.hash(state);
        self.length.hash(state);
    }
}

#[cfg(feature = "vm")]
impl PartialEq for StaticGuestSlice {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.module, &other.module)
            && self.segment == other.segment
            && self.offset == other.offset
            && self.length == other.length
    }
}

#[cfg(feature = "vm")]
impl Eq for StaticGuestSlice {}

#[cfg(feature = "vm")]
impl StaticGuestSlice {
    /// Attempts to locate a data segment that spans the provided linear memory
    /// offset and length. If one is found, returns `Some(StaticGuestSlice)`
    /// that refers to the span (and that can be `resolve`d to yield the bytes of
    /// it), otherwise returns None.
    fn new(module: Arc<wasmi::Module>, mem_off: u32, length: u32) -> Option<Self> {
        let Some(mem_end) = mem_off.checked_add(length) else {
            return None;
        };
        for (segment, seg) in module.data_segments().iter().enumerate() {
            let Some(off_op) = seg.offset().operators().get(0) else {
                continue;
            };
            let Some(seg_off) = off_op.as_const_i32() else {
                continue;
            };
            // WASM interprets the offset i32 as a u32.
            let seg_off = seg_off as u32;

            // If somehow the len was > u32::max, return.
            let seg_len = seg.data().len() as u32;
            if seg_len as usize != seg.data().len() {
                continue;
            }
            let Some(seg_end) = seg_off.checked_add(seg_len) else {
                continue;
            };
            if seg_off <= mem_off && mem_off < seg_end && seg_off < mem_end && mem_end <= seg_end {
                let offset = mem_off - seg_off;
                return Some(Self {
                    module,
                    segment,
                    offset,
                    length,
                });
            }
        }
        None
    }

    fn resolve(&self) -> Result<&[u8], HostError> {
        let Some(seg) = self.module.data_segments().get(self.segment) else {
            return Err(xdr::ScHostObjErrorCode::UnknownError.into());
        };
        let off = self.offset as usize;
        let len = self.length as usize;
        let range = off..off + len;
        seg.data()
            .get(range)
            .ok_or_else(|| xdr::ScHostObjErrorCode::UnknownError.into())
    }
}

#[derive(Clone, Debug)]
pub(crate) enum StaticSlice {
    /// A native static slice in the current binary.
    Native(&'static [u8]),

    /// A static slice defined by guest code that refers into one of the data
    /// segments of the guest's wasm module.
    #[cfg(feature = "vm")]
    Guest(StaticGuestSlice),
}

impl std::hash::Hash for StaticSlice {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            StaticSlice::Native(ss) => {
                ss.as_ptr().hash(state);
                ss.len().hash(state)
            }

            #[cfg(feature = "vm")]
            StaticSlice::Guest(g) => g.hash(state),
        }
    }
}

impl PartialEq for StaticSlice {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Native(l0), Self::Native(r0)) => {
                l0.as_ptr() == r0.as_ptr() && l0.len() == r0.len()
            }

            #[cfg(feature = "vm")]
            (Self::Guest(l0), Self::Guest(r0)) => l0 == r0,

            #[cfg(feature = "vm")]
            _ => false,
        }
    }
}

#[derive(Clone)]
pub(crate) enum HostObject {
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
    BytesStatic(StaticSlice),
    String(xdr::ScString),
    StringStatic(StaticSlice),
    Symbol(xdr::ScSymbol),
    SymbolStatic(StaticSlice),
    ContractExecutable(xdr::ScContractExecutable),
    Address(xdr::ScAddress),
    NonceKey(ScNonceKey),
}

// Host objects implement Hash and Eq _trivially_ / cheaply / partially, for the
// purposes of partially interning objects that are trivially equal (every copy
// of the same number, same address, same static slice, etc.)
//
// These do _not_ do a complete / expensive / deep structural comparison, and
// RawVals are not "interned" in the sense that 2 shallow/bitwise-unequal
// RawVals are necessarily _structurally_ unequal; they might refer to objects
// that are structurally equal, but the trivial Eq-equality in the host object
// hashtable didn't catch it (eg. 2 strings with the same content stored at
// different locations in static memory).

impl std::hash::Hash for HostObject {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            // There's nothing more trivial we can use from these types. If in
            // the future they become (Rc<thing>,pos,len) or something we can
            // hash the pointer, pos, len.
            HostObject::Vec(_)
            | HostObject::Map(_)
            | HostObject::Bytes(_)
            | HostObject::String(_)
            | HostObject::Symbol(_) => (),

            // Numbers all have trivial hash functions.
            HostObject::U64(n) => n.hash(state),
            HostObject::I64(n) => n.hash(state),
            HostObject::TimePoint(n) => n.hash(state),
            HostObject::Duration(n) => n.hash(state),
            HostObject::U128(n) => n.hash(state),
            HostObject::I128(n) => n.hash(state),
            HostObject::U256(n) => n.hash(state),
            HostObject::I256(n) => n.hash(state),

            // Static slices hash and compare their pointers and lengths.
            HostObject::BytesStatic(n) => n.hash(state),
            HostObject::StringStatic(n) => n.hash(state),
            HostObject::SymbolStatic(n) => n.hash(state),

            // Fixed-size (usually 32-byte) objects hash and compare values.
            HostObject::ContractExecutable(n) => n.hash(state),
            HostObject::Address(n) => n.hash(state),
            HostObject::NonceKey(n) => n.hash(state),
        }
    }
}

pub struct HostObjectPool {
    set: indexmap::IndexSet<HostObject>,
}

pub(crate) trait HostObjectType: Sized {
    fn inject(self) -> HostObject;
    fn try_extract(obj: &HostObject) -> Option<&Self>;
}

macro_rules! declare_host_object_type {
    ($TY:ty, $CASE:ident) => {
        impl HostObjectType for $TY {
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

// ${type of contained data}, ${identifier for ScObject}, ${case in HostObject}
declare_host_object_type!(HostMap, Map);
declare_host_object_type!(HostVec, Vec);
declare_host_object_type!(u64, U64);
declare_host_object_type!(i64, I64);
declare_host_object_type!(xdr::TimePoint, TimePoint);
declare_host_object_type!(xdr::Duration, Duration);
declare_host_object_type!(u128, U128);
declare_host_object_type!(i128, I128);
declare_host_object_type!(xdr::ScBytes, Bytes);
declare_host_object_type!(xdr::ScString, String);
declare_host_object_type!(xdr::ScSymbol, Symbol);
declare_host_object_type!(xdr::ScContractExecutable, ContractExecutable);
declare_host_object_type!(xdr::ScAddress, Address);
declare_host_object_type!(ScNonceKey, NonceKey);
