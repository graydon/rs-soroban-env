use crate::{
    budget::AsBudget,
    events::Events,
    xdr::{self, ScError},
    Error, Host,
};
use backtrace::{Backtrace, BacktraceFrame};
use core::fmt::Debug;
use soroban_env_common::{
    xdr::{ScErrorCode, ScErrorType},
    RawVal,
};
use std::ops::DerefMut;

#[derive(Clone)]
struct DebugInfo {
    events: Events,
    backtrace: Backtrace,
}

#[derive(Clone)]
pub struct HostError {
    pub error: Error,
    pub(crate) info: Option<Box<DebugInfo>>,
}

impl std::error::Error for HostError {}

impl Debug for HostError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // We do a little trimming here, skipping the first two frames (which
        // are always into, from, and one or more Host::err_foo calls) and all
        // the frames _after_ the short-backtrace marker that rust compiles-in.

        fn frame_name_matches(frame: &BacktraceFrame, pat: &str) -> bool {
            for sym in frame.symbols() {
                match sym.name() {
                    Some(sn) if format!("{:}", sn).contains(pat) => {
                        return true;
                    }
                    _ => (),
                }
            }
            false
        }

        fn frame_is_short_backtrace_start(frame: &BacktraceFrame) -> bool {
            frame_name_matches(frame, "__rust_begin_short_backtrace")
        }

        fn frame_is_initial_error_plumbing(frame: &BacktraceFrame) -> bool {
            frame_name_matches(frame, "::from")
                || frame_name_matches(frame, "::into")
                || frame_name_matches(frame, "Host::err")
                || frame_name_matches(frame, "::map_err")
        }

        writeln!(f, "HostError: {:?}", self.error)?;
        if let Some(info) = self.info {
            let mut bt = info.backtrace.clone();
            bt.resolve();
            let frames: Vec<BacktraceFrame> = bt
                .frames()
                .iter()
                .skip_while(|f| frame_is_initial_error_plumbing(f))
                .take_while(|f| !frame_is_short_backtrace_start(f))
                .cloned()
                .collect();
            let bt: Backtrace = frames.into();
            // TODO: maybe make this something users can adjust?
            const MAX_EVENTS: usize = 25;
            let mut wrote_heading = false;
            for (i, e) in info
                .events
                .0
                .iter()
                .rev()
                .map(|e| format!("{:?}", e))
                .take(MAX_EVENTS)
                .enumerate()
            {
                if !wrote_heading {
                    writeln!(f)?;
                    writeln!(f, "Event log (newest first):")?;
                    wrote_heading = true;
                }
                writeln!(f, "   {:?}: {:?}", i, e)?;
            }
            if info.events.0.len() > MAX_EVENTS {
                writeln!(f, "   {:?}: ... elided ...", MAX_EVENTS)?;
            }
            writeln!(f)?;
            writeln!(f, "Backtrace (newest first):")?;
            writeln!(f, "{:?}", bt)
        } else {
            writeln!(f, "DebugInfo not available")
        }
    }
}

impl HostError {
    #[cfg(test)]
    pub fn result_matches_err_status<T, C>(res: Result<T, HostError>, code: C) -> bool
    where
        Error: From<C>,
    {
        match res {
            Ok(_) => false,
            Err(he) => {
                let status: Error = code.into();
                he.status == status
            }
        }
    }
}

impl<T> From<T> for HostError
where
    Error: From<T>,
{
    fn from(error: T) -> Self {
        let error = error.into();
        Self { error, info: None }
    }
}

impl std::fmt::Display for HostError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <HostError as Debug>::fmt(self, f)
    }
}

impl TryFrom<&HostError> for ScError {
    type Error = xdr::Error;
    fn try_from(err: &HostError) -> Result<Self, Self::Error> {
        err.error.try_into()
    }
}

impl From<HostError> for std::io::Error {
    fn from(e: HostError) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, e)
    }
}

impl Host {
    /// Convenience function that only evaluates non-[Error] args to [Host::err]
    /// when [Host::is_debug] is `true`.
    pub fn err_lazy<'a>(
        &self,
        type_: ScErrorType,
        code: ScErrorCode,
        msg: &str,
        debug_args: impl FnOnce() -> &'a [RawVal] + 'a,
    ) -> HostError {
        if self.is_debug() {
            self.err(type_, code, msg, debug_args())
        } else {
            self.err(type_, code, msg, &[])
        }
    }

    /// Convenience function to construct an [Error] and pass to [Host::error].
    pub fn err(
        &self,
        type_: ScErrorType,
        code: ScErrorCode,
        msg: &str,
        args: &[RawVal],
    ) -> HostError {
        let error = Error::from_type_and_code(type_, code);
        self.error(error, msg, args)
    }

    /// When the host is running at [DiagnosticLevel::Debug], records a
    /// [ContractEventType::Diagnostic] event with the provided [Error] and
    /// arguments, then captures a [Backtrace] and snapshot of the [Events]
    /// buffer into a [DebugInfo], and returns a [HostError] carrying both the
    /// [Error] and [DebugInfo]. When running at [DiagnosticLevel::None], just
    /// returns a [HostError] with the provided [Error], recording no event and
    /// constructing no [DebugInfo].
    pub fn error(&self, error: Error, msg: &str, args: &[RawVal]) -> HostError {
        if self.is_debug() {
            // We _try_ to take a mutable borrow of the events buffer refcell
            // while building up the event we're going to emit into the events
            // log, failing gracefully (just emitting a no-debug-info
            // `HostError` wrapping the supplied `Error`) if we cannot acquire
            // the refcell. This is to handle the "double fault" case where we
            // get an error _while performing_ any of the steps needed to record
            // an error as an event, below.
            if let Ok(mut events_refmut) = self.0.events.try_borrow_mut() {
                if let Err(e) = self.err_diagnostics(events_refmut.deref_mut(), error, msg, args) {
                    return e;
                }
                let events = match self
                    .as_budget()
                    .with_free_budget(|| events_refmut.externalize(self))
                {
                    Ok(events) => events,
                    Err(e) => return e,
                };
                let backtrace = Backtrace::new_unresolved();
                let info = Some(Box::new(DebugInfo { backtrace, events }));
                return HostError { error, info };
            }
        }
        error.into()
    }

    /// Given a result carrying some error type that can be converted to an
    /// [Error] and supports [core::fmt::Debug], calls [Host::error] with the
    /// error when there's an error, also passing the result of
    /// [core::fmt::Debug::fmt] when [Host::is_debug] is `true`. Returns a
    /// [Result] over [HostError].
    ///
    /// If you have an error type `T` you want to record as a detailed debug
    /// event and a less-detailed [Error] code embedded in a [HostError], add an
    /// `impl From<T> for Error` over in `soroban_env_common::error`, or in the
    /// module defining `T`, and call this where the error is generated.
    ///
    /// Note: we do _not_ want to `impl From<T> for HostError` for such types,
    /// as doing so will avoid routing them through the host in order to record
    /// their extended diagnostic information into the event log. This means you
    /// will wind up writing `host.map_err(...)?` a bunch in code that you used
    /// to be able to get away with just writing `...?`, there's no way around
    /// this if we want to record the diagnostic information.
    pub fn map_err<T, E>(&self, res: Result<T, E>) -> Result<T, HostError>
    where
        Error: From<E>,
        E: Debug,
    {
        res.map_err(|e| {
            if self.is_debug() {
                let msg = format!("{:?}", e);
                self.error(e.into(), &msg, &[])
            } else {
                self.error(e.into(), "", &[])
            }
        })
    }
}

// Helper for building multi-argument errors.
// For example:
// ```
// err!(host, status, "{}: foo {}", arg1, arg2);
// ```
// All arguments must be convertible to `RawVal` with `try_into_val`. This is
// expected to be called from within a function that returns
// `Result<_, HostError>`. If these requirements can't be fulfilled, use
// `err_status_msg_with_args` function directly.
#[macro_export]
macro_rules! err {
    ($host:expr, $ty:expr, $code:expr, $msg:expr, $($args:expr),+) => {
        $host.err($ty, $code, $msg, &[$($args.try_into_val($host)?,)+])
    };
}
