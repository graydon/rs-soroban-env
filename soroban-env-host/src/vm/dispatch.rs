use super::FuelRefillable;
use crate::vm::SendHost;
use crate::{
    xdr::{ContractCostType, ScErrorCode, ScErrorType},
    CheckedEnvArg, EnvBase, Host, HostError, VmContextEnv,
};
use crate::{
    AddressObject, Bool, BytesObject, ContractTtlExtension, DurationObject, Error, ErrorHandler,
    I128Object, I256Object, I256Val, I64Object, MapObject, MuxedAddressObject, StorageType,
    StringObject, Symbol, SymbolObject, TimepointObject, U128Object, U256Object, U256Val, U32Val,
    U64Object, U64Val, Val, VecObject, Void,
};
use core::fmt::Debug;
use soroban_env_common::call_macro_with_all_host_functions;

#[cfg(feature = "wasmi")]
use soroban_env_common::WasmiMarshal;

#[cfg(feature = "wasmtime")]
use soroban_env_common::WasmtimeMarshal;

pub(crate) trait RelativeObjectConversionBase: Sized {
    fn absolute_to_relative(self, _host: &Host) -> Result<Self, HostError> {
        Ok(self)
    }
    fn relative_to_absolute(self, _host: &Host) -> Result<Self, HostError> {
        Ok(self)
    }
}

#[cfg(feature = "wasmi")]
trait WasmiRelativeObjectConversion: RelativeObjectConversionBase + WasmiMarshal {
    fn try_marshal_from_relative_wasmi_value(
        v: wasmi::Value,
        host: &Host,
    ) -> Result<Self, wasmi::core::Trap> {
        let val = Self::try_marshal_from_value(v).ok_or_else(|| {
            wasmi::core::Trap::from(HostError::from(Error::from_type_and_code(
                ScErrorType::Value,
                ScErrorCode::InvalidInput,
            )))
        })?;
        Ok(val.relative_to_absolute(host)?)
    }
    fn marshal_relative_wasmi_value_from_self(
        self,
        host: &Host,
    ) -> Result<wasmi::Value, wasmi::core::Trap> {
        let rel = self.absolute_to_relative(host)?;
        Ok(Self::marshal_from_self(rel))
    }
}

#[cfg(feature = "wasmtime")]
trait WasmtimeRelativeObjectConversion: RelativeObjectConversionBase + WasmtimeMarshal {
    fn try_marshal_from_relative_wasmtime_value(
        v: wasmtime::Val,
        host: &Host,
    ) -> Result<Self, wasmtime::Error> {
        let val = Self::try_marshal_from_wasmtime_value(v).ok_or_else(|| {
            wasmtime::Error::from(HostError::from(Error::from_type_and_code(
                ScErrorType::Value,
                ScErrorCode::InvalidInput,
            )))
        })?;
        Ok(val.relative_to_absolute(host)?)
    }
    fn marshal_relative_wasmtime_value_from_self(
        self,
        host: &Host,
    ) -> Result<wasmtime::Val, wasmtime::Error> {
        let rel = self.absolute_to_relative(host)?;
        Ok(Self::marshal_wasmtime_from_self(rel))
    }
}

macro_rules! impl_relative_object_conversion {
    ($T:ty) => {
        impl RelativeObjectConversionBase for $T {
            fn absolute_to_relative(self, host: &Host) -> Result<Self, HostError> {
                Ok(Self::try_from(host.absolute_to_relative(self.into())?)?)
            }

            fn relative_to_absolute(self, host: &Host) -> Result<Self, HostError> {
                Ok(Self::try_from(host.relative_to_absolute(self.into())?)?)
            }
        }
        #[cfg(feature = "wasmi")]
        impl WasmiRelativeObjectConversion for $T {}
        #[cfg(feature = "wasmtime")]
        impl WasmtimeRelativeObjectConversion for $T {}
    };
}

enum TraceArg<T: Debug> {
    Bad(i64),
    Ok(T),
}
impl<T> Debug for TraceArg<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TraceArg::Bad(i) => write!(f, "bad:{:?}", i),
            TraceArg::Ok(t) => write!(f, "{:?}", t),
        }
    }
}

macro_rules! homogenize_tuple {
    ($u:ident, ()) => {
        &[]
    };
    ($u:ident, ($_a:expr)) => {
        &[&$u]
    };
    ($u:ident, ($_a:expr, $_b:expr)) => {
        &[&$u.0, &$u.1]
    };
    ($u:ident, ($_a:expr, $_b:expr, $_c:expr)) => {
        &[&$u.0, &$u.1, &$u.2]
    };
    ($u:ident, ($_a:expr, $_b:expr, $_c:expr, $_d:expr)) => {
        &[&$u.0, &$u.1, &$u.2, &$u.3]
    };
    ($u:ident, ($_a:expr, $_b:expr, $_c:expr, $_d:expr, $_e:expr)) => {
        &[&$u.0, &$u.1, &$u.2, &$u.3, &$u.4]
    };
    ($u:ident, ($_a:expr, $_b:expr, $_c:expr, $_d:expr, $_e:expr, $_f:expr)) => {
        &[&$u.0, &$u.1, &$u.2, &$u.3, &$u.4, &$u.5]
    };
    ($u:ident, ($_a:expr, $_b:expr, $_c:expr, $_d:expr, $_e:expr, $_f:expr, $_g:expr)) => {
        &[&$u.0, &$u.1, &$u.2, &$u.3, &$u.4, &$u.5, &$u.6]
    };
    ($u:ident, ($_a:expr, $_b:expr, $_c:expr, $_d:expr, $_e:expr, $_f:expr, $_g:expr, $_h:expr)) => {
        &[&$u.0, &$u.1, &$u.2, &$u.3, &$u.4, &$u.5, &$u.6, &$u.7]
    };
}

// Define a relative-to-absolute impl for any type that is (a) mentioned
// in a host function type signature in env and (b) might possibly carry an
// object reference. If you miss one, this file won't compile, so it's safe.
impl_relative_object_conversion!(Val);
impl_relative_object_conversion!(Symbol);

impl_relative_object_conversion!(AddressObject);
impl_relative_object_conversion!(MuxedAddressObject);
impl_relative_object_conversion!(BytesObject);
impl_relative_object_conversion!(DurationObject);

impl_relative_object_conversion!(TimepointObject);
impl_relative_object_conversion!(SymbolObject);
impl_relative_object_conversion!(StringObject);

impl_relative_object_conversion!(VecObject);
impl_relative_object_conversion!(MapObject);

impl_relative_object_conversion!(I64Object);
impl_relative_object_conversion!(I128Object);
impl_relative_object_conversion!(I256Object);

impl_relative_object_conversion!(U64Object);
impl_relative_object_conversion!(U128Object);
impl_relative_object_conversion!(U256Object);

impl_relative_object_conversion!(U64Val);
impl_relative_object_conversion!(U256Val);
impl_relative_object_conversion!(I256Val);

// Trivial / non-relativizing impls are ok for types that can't carry objects.
impl RelativeObjectConversionBase for i64 {}
impl RelativeObjectConversionBase for u64 {}
impl RelativeObjectConversionBase for Void {}
impl RelativeObjectConversionBase for Bool {}
impl RelativeObjectConversionBase for Error {}
impl RelativeObjectConversionBase for StorageType {}
impl RelativeObjectConversionBase for ContractTtlExtension {}
impl RelativeObjectConversionBase for U32Val {}

#[cfg(feature = "wasmi")]
pub(crate) mod wasmi_dispatch {
    use super::*;
    use wasmi::AsContextMut;

    impl WasmiRelativeObjectConversion for i64 {}
    impl WasmiRelativeObjectConversion for u64 {}
    impl WasmiRelativeObjectConversion for Void {}
    impl WasmiRelativeObjectConversion for Bool {}
    impl WasmiRelativeObjectConversion for Error {}
    impl WasmiRelativeObjectConversion for StorageType {}
    impl WasmiRelativeObjectConversion for ContractTtlExtension {}
    impl WasmiRelativeObjectConversion for U32Val {}

    struct CallerFuelTransfer<'a> {
        caller: wasmi::Caller<'a, SendHost>,
        host: SendHost,
        finished: bool,
    }

    impl<'a> CallerFuelTransfer<'a> {
        fn new(mut caller: wasmi::Caller<'a, SendHost>) -> Result<Self, wasmi::core::Trap> {
            let host = caller.data().clone();
            let last_fuel = host.take_last_vm_fuel()?;
            FuelRefillable::return_fuel_to_host(&mut caller, &host, last_fuel)
                .map_err(|he| wasmi::core::Trap::from(he))?;
            Ok(Self {
                caller,
                host,
                finished: false,
            })
        }
        fn fini(&mut self) -> Result<(), wasmi::core::Trap> {
            let added_fuel = FuelRefillable::add_fuel_to_vm(&mut self.caller, &self.host)
                .map_err(|he| wasmi::core::Trap::from(he))?;
            self.host
                .save_last_vm_fuel(added_fuel)
                .map_err(|he| wasmi::core::Trap::from(he))?;
            self.finished = true;
            Ok(())
        }
    }
    impl<'a> Drop for CallerFuelTransfer<'a> {
        fn drop(&mut self) {
            if self.finished {
                return;
            }
            // This is a fairly last-ditch path we run only when we are already
            // backing out of a dispatch method with an error anyways (the regular
            // path calls fini on success), and while it might kinda be nice to pick
            // up errors from here as well, we can't do so from a dtor. Our best
            // effort is to at least restore the vm's fuel and make a note about the
            // update in last_vm_fuel, which doesn't have a _lot_ of ways of
            // failing.
            let _ = self.fini();
        }
    }

    ///////////////////////////////////////////////////////////////////////////////
    /// X-macro use: dispatch functions
    ///////////////////////////////////////////////////////////////////////////////
    //
    // This is a callback macro that pattern-matches the token-tree passed by the
    // x-macro (call_macro_with_all_host_functions) and produces a suite of
    // dispatch-function definitions.
    macro_rules! generate_wasmi_dispatch_functions {
    {
        $(
            // This outer pattern matches a single 'mod' block of the token-tree
            // passed from the x-macro to this macro. It is embedded in a `$()*`
            // pattern-repetition matcher so that it will match all provided
            // 'mod' blocks provided.
            $(#[$mod_attr:meta])*
            mod $mod_name:ident $mod_str:literal
            {
                $(
                    // This inner pattern matches a single function description
                    // inside a 'mod' block in the token-tree passed from the
                    // x-macro to this macro. It is embedded in a `$()*`
                    // pattern-repetition matcher so that it will match all such
                    // descriptions.
                    $(#[$fn_attr:meta])*
                    { $fn_str:literal, $($min_proto:literal)?, $($max_proto:literal)?, fn $fn_id:ident ($($arg:ident:$type:ty),*) -> $ret:ty }
                )*
            }
        )*
    }

    =>  // The part of the macro above this line is a matcher; below is its expansion.

    {
        // This macro expands to multiple items: a set of free functions in the
        // current module, which are called by functions registered with the VM
        // to forward calls to the host.
        $(
            $(
                // This defines a "dispatch function" that does several things:
                //
                //  1. Transfers the running "VM fuel" balance from wasmi to the
                //     host's CPU budget.
                //  2. Charges the host budget for the call, failing if over.
                //  3. Attempts to convert incoming wasmi i64 args to Vals or
                //     Val-wrappers expected by host functions, failing if any
                //     conversions fail. This step also does
                //     relative-to-absolute object reference conversion.
                //  4. Calls the host function.
                //  5. Augments any error result with this calling context, so
                //     that we get at minimum a "which host function failed"
                //     context on error.
                //  6. Converts the result back to an i64 for wasmi, again
                //     converting from absolute object references to relative
                //     along the way.
                //  7. Checks the result is Ok, or escalates Err to a VM Trap.
                //  8. Transfers the residual CPU budget back to wasmi "VM
                //     fuel".
                //
                // It is embedded in two nested `$()*` pattern-repetition
                // expanders that correspond to the pattern-repetition matchers
                // in the match section, but we ignore the structure of the
                // 'mod' block repetition-level from the outer pattern in the
                // expansion, flattening all functions from all 'mod' blocks
                // into a set of functions.
                $(#[$fn_attr])*
                pub(crate) fn $fn_id(caller: wasmi::Caller<SendHost>, $($arg:i64),*) ->
                    Result<(i64,), wasmi::core::Trap>
                {
                    let _span = tracy_span!(core::stringify!($fn_id));

                    let host = caller.data().clone();

                    // This is an additional protocol version guardrail that
                    // should not be necessary. Any wasm contract containing a
                    // call to an out-of-protocol-range host function should
                    // have been rejected by the linker during VM instantiation.
                    // This is just an additional guard rail for future proof.
                    $( host.check_protocol_version_lower_bound($min_proto)?; )?
                    $( host.check_protocol_version_upper_bound($max_proto)?; )?

                    // This is where the VM -> Host boundary is crossed.
                    // We first return all fuel from the VM back to the host such that
                    // the host maintains control of the budget.
                    let mut fuel_transfer = CallerFuelTransfer::new(caller)?;

                    if host.tracing_enabled()
                    {
                        #[allow(unused)]
                        let trace_args = ($(
                            match <$type>::try_marshal_from_relative_wasmi_value(wasmi::Value::I64($arg), &host) {
                                Ok(val) => TraceArg::Ok(val),
                                Err(_) => TraceArg::Bad($arg),
                            }
                        ),*);
                        let hook_args: &[&dyn std::fmt::Debug] = homogenize_tuple!(trace_args, ($($arg),*));
                        let vmctx = fuel_transfer.caller.as_context_mut();
                        host.trace_env_call_with_vmcontext(
                            &core::stringify!($fn_id),
                            hook_args,
                            vmctx.into(),
                        )?;
                    }

                    // Charge for the host function dispatching: conversion between VM fuel and
                    // host budget, marshalling values. This does not account for the actual work
                    // being done in those functions, which are metered individually by the implementation.
                    host.charge_budget(ContractCostType::DispatchHostFunction, None)?;

                    // The odd / seemingly-redundant use of `wasmi::Value` here
                    // as intermediates -- rather than just passing Vals --
                    // has to do with the fact that some host functions are
                    // typed as receiving or returning plain _non-val_ i64 or
                    // u64 values. So the call here has to be able to massage
                    // both types into and out of i64, and `wasmi::Value`
                    // happens to be a natural switching point for that: we have
                    // conversions to and from both Val and i64 / u64 for
                    // wasmi::Value.
                    let vmctx = fuel_transfer.caller.as_context_mut();
                    let res: Result<_, HostError> = host.$fn_id(vmctx.into(), $(<$type>::check_env_arg(<$type>::try_marshal_from_relative_wasmi_value(wasmi::Value::I64($arg), &host)?, &host.0)?),*);

                    if host.tracing_enabled()
                    {
                        let dyn_res: Result<&dyn core::fmt::Debug,&HostError> = match &res {
                            Ok(ref ok) => Ok(ok),
                            Err(err) => Err(err)
                        };
                        let vmctx = fuel_transfer.caller.as_context_mut();
                        host.trace_env_ret_with_vmcontext(
                            &core::stringify!($fn_id),
                            &dyn_res,
                            vmctx.into(),
                        )?;
                    }

                    // On the off chance we got an error with no context, we can
                    // at least attach some here "at each host function call",
                    // fairly systematically. This will cause the context to
                    // propagate back through wasmi to its caller.
                    let res = host.augment_err_result(res);

                    let res = match res {
                        Ok(ok) => {
                            let ok = ok.check_env_arg(&host.0)?;
                            let val: wasmi::Value = ok.marshal_relative_wasmi_value_from_self(&host)?;
                            if let wasmi::Value::I64(v) = val {
                                Ok((v,))
                            } else {
                                Err(wasmi::core::TrapCode::BadSignature.into())
                            }
                        },
                        Err(hosterr) => {
                            // We make a new HostError here to capture the escalation event itself.
                            let escalation: HostError =
                                host.error(hosterr.error,
                                           concat!("escalating error to VM trap from failed host function call: ",
                                                   stringify!($fn_id)), &[]);
                            let trap: wasmi::core::Trap = escalation.into();
                            Err(trap)
                        }
                    };

                    // This is where the Host->VM boundary is crossed. We supply
                    // the remaining host budget as fuel to the VM.
                    //
                    // Note: it is possible we did not get here (if an
                    // arg-marshal step above failed), but the `fuel_transfer`
                    // dtor will try to ensure fini() is called anyways.
                    fuel_transfer.fini()?;

                    res
                }
            )*
        )*
    };
}

    // Here we invoke the x-macro passing generate_dispatch_functions as its callback macro.
    call_macro_with_all_host_functions! { generate_wasmi_dispatch_functions }
}

#[cfg(feature = "wasmtime")]
pub(crate) mod wasmtime_dispatch {
    use super::*;
    use wasmtime::AsContextMut;

    impl WasmtimeRelativeObjectConversion for i64 {}
    impl WasmtimeRelativeObjectConversion for u64 {}
    impl WasmtimeRelativeObjectConversion for Void {}
    impl WasmtimeRelativeObjectConversion for Bool {}
    impl WasmtimeRelativeObjectConversion for Error {}
    impl WasmtimeRelativeObjectConversion for StorageType {}
    impl WasmtimeRelativeObjectConversion for ContractTtlExtension {}
    impl WasmtimeRelativeObjectConversion for U32Val {}

    struct CallerFuelTransfer<'a> {
        caller: wasmtime::Caller<'a, SendHost>,
        host: SendHost,
        finished: bool,
    }

    impl<'a> CallerFuelTransfer<'a> {
        fn new(mut caller: wasmtime::Caller<'a, SendHost>) -> Result<Self, wasmtime::Error> {
            let host = caller.data().clone();
            let last_fuel = host.take_last_vm_fuel()?;
            FuelRefillable::return_fuel_to_host(&mut caller, &host, last_fuel)?;
            Ok(Self {
                caller,
                host,
                finished: false,
            })
        }
        fn fini(&mut self) -> Result<(), wasmtime::Error> {
            let added_fuel = FuelRefillable::add_fuel_to_vm(&mut self.caller, &self.host)?;
            self.host.save_last_vm_fuel(added_fuel)?;
            self.finished = true;
            Ok(())
        }
    }
    impl<'a> Drop for CallerFuelTransfer<'a> {
        fn drop(&mut self) {
            if self.finished {
                return;
            }
            // This is a fairly last-ditch path we run only when we are already
            // backing out of a dispatch method with an error anyways (the regular
            // path calls fini on success), and while it might kinda be nice to pick
            // up errors from here as well, we can't do so from a dtor. Our best
            // effort is to at least restore the vm's fuel and make a note about the
            // update in last_vm_fuel, which doesn't have a _lot_ of ways of
            // failing.
            let _ = self.fini();
        }
    }

    ///////////////////////////////////////////////////////////////////////////////
    /// X-macro use: dispatch functions
    ///////////////////////////////////////////////////////////////////////////////

    // This is a callback macro that pattern-matches the token-tree passed by the
    // x-macro (call_macro_with_all_host_functions) and produces a suite of
    // dispatch-function definitions.
    macro_rules! generate_wasmtime_dispatch_functions {
    {
        $(
            // This outer pattern matches a single 'mod' block of the token-tree
            // passed from the x-macro to this macro. It is embedded in a `$()*`
            // pattern-repetition matcher so that it will match all provided
            // 'mod' blocks provided.
            $(#[$mod_attr:meta])*
            mod $mod_name:ident $mod_str:literal
            {
                $(
                    // This inner pattern matches a single function description
                    // inside a 'mod' block in the token-tree passed from the
                    // x-macro to this macro. It is embedded in a `$()*`
                    // pattern-repetition matcher so that it will match all such
                    // descriptions.
                    $(#[$fn_attr:meta])*
                    { $fn_str:literal, $($min_proto:literal)?, $($max_proto:literal)?, fn $fn_id:ident ($($arg:ident:$type:ty),*) -> $ret:ty }
                )*
            }
        )*
    }

    =>  // The part of the macro above this line is a matcher; below is its expansion.

    {
        // This macro expands to multiple items: a set of free functions in the
        // current module, which are called by functions registered with the VM
        // to forward calls to the host.
        $(
            $(
                // This defines a "dispatch function" that does several things:
                //
                //  1. Transfers the running "VM fuel" balance from wasmi to the
                //     host's CPU budget.
                //  2. Charges the host budget for the call, failing if over.
                //  3. Attempts to convert incoming wasmi i64 args to Vals or
                //     Val-wrappers expected by host functions, failing if any
                //     conversions fail. This step also does
                //     relative-to-absolute object reference conversion.
                //  4. Calls the host function.
                //  5. Augments any error result with this calling context, so
                //     that we get at minimum a "which host function failed"
                //     context on error.
                //  6. Converts the result back to an i64 for wasmi, again
                //     converting from absolute object references to relative
                //     along the way.
                //  7. Checks the result is Ok, or escalates Err to a VM Trap.
                //  8. Transfers the residual CPU budget back to wasmi "VM
                //     fuel".
                //
                // It is embedded in two nested `$()*` pattern-repetition
                // expanders that correspond to the pattern-repetition matchers
                // in the match section, but we ignore the structure of the
                // 'mod' block repetition-level from the outer pattern in the
                // expansion, flattening all functions from all 'mod' blocks
                // into a set of functions.
                $(#[$fn_attr])*
                pub(crate) fn $fn_id(caller: wasmtime::Caller<'_, SendHost>, $($arg:i64),*) ->
                    Result<(i64,), wasmtime::Error>
                {
                    let _span = tracy_span!(core::stringify!($fn_id));

                    let host = caller.data().clone();

                    // This is an additional protocol version guardrail that
                    // should not be necessary. Any wasm contract containing a
                    // call to an out-of-protocol-range host function should
                    // have been rejected by the linker during VM instantiation.
                    // This is just an additional guard rail for future proof.
                    $( host.check_protocol_version_lower_bound($min_proto)?; )?
                    $( host.check_protocol_version_upper_bound($max_proto)?; )?

                    // This is where the VM -> Host boundary is crossed.
                    // We first return all fuel from the VM back to the host such that
                    // the host maintains control of the budget.
                    let mut fuel_transfer = CallerFuelTransfer::new(caller)?;

                    if host.tracing_enabled()
                    {
                        #[allow(unused)]
                        let trace_args = ($(
                            match <$type>::try_marshal_from_relative_wasmtime_value(wasmtime::Val::I64($arg), &host) {
                                Ok(val) => TraceArg::Ok(val),
                                Err(_) => TraceArg::Bad($arg),
                            }
                        ),*);
                        let hook_args: &[&dyn std::fmt::Debug] = homogenize_tuple!(trace_args, ($($arg),*));
                        let vmctx = fuel_transfer.caller.as_context_mut();
                        host.trace_env_call_with_vmcontext(
                            &core::stringify!($fn_id),
                            hook_args,
                            vmctx.into(),
                        )?;
                    }

                    // Charge for the host function dispatching: conversion between VM fuel and
                    // host budget, marshalling values. This does not account for the actual work
                    // being done in those functions, which are metered individually by the implementation.
                    host.charge_budget(ContractCostType::DispatchHostFunction, None)?;

                    // The odd / seemingly-redundant use of `wasmi::Value` here
                    // as intermediates -- rather than just passing Vals --
                    // has to do with the fact that some host functions are
                    // typed as receiving or returning plain _non-val_ i64 or
                    // u64 values. So the call here has to be able to massage
                    // both types into and out of i64, and `wasmi::Value`
                    // happens to be a natural switching point for that: we have
                    // conversions to and from both Val and i64 / u64 for
                    // wasmi::Value.
                    let vmctx = fuel_transfer.caller.as_context_mut();
                    let res: Result<_, HostError> = host.$fn_id(vmctx.into(), $(<$type>::check_env_arg(<$type>::try_marshal_from_relative_wasmtime_value(wasmtime::Val::I64($arg), &host)?, &host.0)?),*);

                    if host.tracing_enabled()
                    {
                        let dyn_res: Result<&dyn core::fmt::Debug,&HostError> = match &res {
                            Ok(ref ok) => Ok(ok),
                            Err(err) => Err(err)
                        };
                        let vmctx = fuel_transfer.caller.as_context_mut();
                        host.trace_env_ret_with_vmcontext(
                            &core::stringify!($fn_id),
                            &dyn_res,
                            vmctx.into(),
                        )?;
                    }

                    // On the off chance we got an error with no context, we can
                    // at least attach some here "at each host function call",
                    // fairly systematically. This will cause the context to
                    // propagate back through wasmi to its caller.
                    let res = host.augment_err_result(res);

                    let res = match res {
                        Ok(ok) => {
                            let ok = ok.check_env_arg(&host.0)?;
                            let val: wasmtime::Val = ok.marshal_relative_wasmtime_value_from_self(&host)?;
                            if let wasmtime::Val::I64(v) = val {
                                Ok((v,))
                            } else {
                                Err(wasmtime::Error::from(wasmtime::Trap::BadSignature))
                            }
                        },
                        Err(hosterr) => {
                            // We make a new HostError here to capture the escalation event itself.
                            let escalation: HostError =
                                host.error(hosterr.error,
                                           concat!("escalating error to VM trap from failed host function call: ",
                                                   stringify!($fn_id)), &[]);
                            Err(escalation.into())
                        }
                    };

                    // This is where the Host->VM boundary is crossed. We supply
                    // the remaining host budget as fuel to the VM.
                    //
                    // Note: it is possible we did not get here (if an
                    // arg-marshal step above failed), but the `fuel_transfer`
                    // dtor will try to ensure fini() is called anyways.
                    fuel_transfer.fini()?;

                    Ok(res?)
                }
            )*
        )*
    };
}

    call_macro_with_all_host_functions! { generate_wasmtime_dispatch_functions }
}
