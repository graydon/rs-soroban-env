#![allow(dead_code)]

use log::debug;
use stellar_contract_env_common::{
    xdr::{self},
    RawVal, Status,
};
use tinyvec::TinyVec;

// TODO: update this when ContractEvent shows up in the XDR defns.
// TODO: optimize storage on this to use pools / bumpalo / etc.
#[derive(Clone, Debug)]
pub(crate) enum HostEvent {
    Contract(/*ContractEvent*/),
    Debug(DebugEvent),
}

#[derive(Clone, Debug, Default)]
pub struct Events(Vec<HostEvent>);

impl Events {
    // Records the smallest variant of a debug HostEvent it can, returning the size of the
    // in_args slice (for charging to a budget).
    pub(crate) fn record_debug_event(&mut self, de: DebugEvent) -> u64 {
        let len = de.args.len();
        self.0.push(HostEvent::Debug(de));
        len as u64
    }

    pub fn dump_to_debug_log(&self) {
        for e in self.0 {
            match e {
                HostEvent::Contract() => debug!("Contract event: <TBD>"),
                HostEvent::Debug(e) => debug!("Debug event: {:?}", e),
            }
        }
    }
}

/// A cheap record type to store in the events buffer for diagnostic reporting
/// when something goes wrong. Should cost very little even when enabled. See
/// [host::debug_event] for normal use.
#[derive(Clone, Debug)]
pub(crate) struct DebugEvent {
    pub(crate) msg: &'static str,
    pub(crate) args: TinyVec<[RawVal; 2]>,
}

impl DebugEvent {
    pub(crate) fn new() -> Self {
        Self {
            msg: "",
            args: Default::default(),
        }
    }

    pub(crate) fn msg(mut self, msg: &'static str) -> Self {
        self.msg = msg;
        self
    }

    pub(crate) fn arg<T>(mut self, arg: T) -> Self
    where
        RawVal: From<T>,
    {
        self.args.push(arg.into());
        self
    }
}

/// Combines a [DebugEvent] with a [Status] that created it, typically
/// used as a transient type when recording a (possibly enriched)
/// debug event for a status and then converting the status to a
/// HostError. See [host::err] for normal use.
#[derive(Clone, Debug)]
pub(crate) struct DebugError {
    pub(crate) event: DebugEvent,
    pub(crate) status: Status,
}

impl DebugError {
    pub(crate) fn new<T>(status: T) -> Self
    where
        Status: From<T>,
    {
        let status: Status = status.into();
        Self {
            event: DebugEvent::new().msg("status").arg::<Status>(status.into()),
            status: status,
        }
    }

    pub(crate) fn general() -> Self {
        Self::new(xdr::ScUnknownErrorCode::General)
    }

    pub(crate) fn msg(mut self, msg: &'static str) -> Self {
        self.event = self.event.msg(msg);
        self
    }

    pub(crate) fn arg<T>(mut self, arg: T) -> Self
    where
        RawVal: From<T>,
    {
        self.event.args.push(arg.into());
        self
    }
}

impl From<xdr::Error> for DebugError {
    fn from(err: xdr::Error) -> Self {
        let msg = match err {
            xdr::Error::Invalid => "XDR error: invalid",
            xdr::Error::LengthExceedsMax => "XDR error: length exceeds max",
            xdr::Error::LengthMismatch => "XDR error: length mismatch",
            xdr::Error::NonZeroPadding => "XDR error: nonzero padding",
            xdr::Error::Utf8Error(_) => "XDR error: UTF-8 error",
            xdr::Error::Io(_) => "XDR error: IO error",
        };
        Self::new(xdr::ScUnknownErrorCode::Xdr).msg(msg)
    }
}
