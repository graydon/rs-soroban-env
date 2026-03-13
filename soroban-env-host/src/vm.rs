//! This module primarily provides the [Vm] type and the necessary name-lookup
//! and runtime-dispatch mechanisms needed to allow WASM modules to call into
//! the [Env](crate::Env) interface implemented by [Host].
//!
//! It also contains helper methods to look up and call into contract functions
//! in terms of [ScVal] and [Val] arguments.
//!
//! The implementation of WASM types and the WASM bytecode interpreter and/or
//! JIT come from the [wasmi](https://github.com/wasmi-labs/wasmi) project
//! and/or the [wasmtime](https://github.com/bytecodealliance/wasmtime) project
//! respectively.
//!
//! The VM can be configured to support either or both engines using feature
//! flags "wasmi" and/or "wasmtime". It must be configured with support for at
//! least _one_, otherwise it will not build.

#[cfg(all(not(feature = "wasmtime"), not(feature = "wasmi")))]
compile_error!("at least one of features 'wasmi' or 'wasmtime' is required");

mod dispatch;
mod fuel_refillable;
mod func_info;
mod module_cache;
mod parsed_module;

#[cfg(feature = "bench")]
pub(crate) use dispatch::dummy0;
#[cfg(all(test, feature = "wasmi"))]
pub(crate) use dispatch::wasmi_dispatch::protocol_gated_dummy;

#[cfg(feature = "wasmi")]
use crate::WasmiMarshal;

#[cfg(feature = "wasmtime")]
use crate::WasmtimeMarshal;
#[cfg(feature = "wasmtime")]
use wasmtime::AsContextMut;

/// SendHost is a wrapper type around Host. It implements `Send` using an
/// `unsafe impl` because technically Host is not Send-safe (in the sense of
/// Rustc's automatic deduction).
///
/// In other words we are lying here, but in a calculated way:
///
///   1. It's a lie we're telling only fulfil a bound on a Wasmtime trait it's
///      awkward and performance-punishing to work around (specifically
///      `ResourceLimiter: Send`)
///
///   2. It's a lie that can only get us into trouble if _we use Wasmtime_ in
///      such a way that it _exploits_ the Send-ness we're lying about.
///
/// We've talked to Wasmtime developers and been assured that Wasmtime will
/// never spawn its own threads or run code on a thread other than the one doing
/// a `Func::call`, and so if we invoke Wasmtime synchronously on a single
/// thread and scope the reachability of a given `SendHost` to just that thread,
/// there is nothing to worry about when making this lie.
///
/// But it means that we _must not_ share `SendHost` or things referencing it
/// between threads in any context. Rust's data-race checking does not have our
/// back here.

#[derive(Clone)]
pub struct SendHost(pub(crate) crate::Host);
impl Deref for SendHost {
    type Target = crate::Host;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl DerefMut for SendHost {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
unsafe impl Send for SendHost {}

use crate::{
    budget::{AsBudget, Budget},
    host::{
        error::TryBorrowOrErr,
        metered_clone::MeteredContainer,
        metered_hash::{CountingHasher, MeteredHash},
    },
    xdr::{ContractCostType, ContractId, ScErrorCode, ScErrorType},
    ConversionError, ErrorHandler, Host, HostError, Symbol, SymbolStr, TryIntoVal, Val, VmContext,
};
use std::{
    cell::RefCell,
    collections::BTreeSet,
    ops::{Deref, DerefMut},
    rc::Rc,
    sync::Arc,
};

use fuel_refillable::FuelRefillable;
use func_info::HOST_FUNCTIONS;

pub use module_cache::ModuleCache;
pub use parsed_module::{
    wasm_module_memory_cost, CompilationContext, ParsedModule, VersionedContractCodeCostInputs,
};

#[cfg(feature = "wasmi")]
impl wasmi::core::HostError for HostError {}

const WASM_STD_MEM_PAGE_SIZE_IN_BYTES: u32 = 0x10000;

struct VmInstantiationTimer {
    #[cfg(not(target_family = "wasm"))]
    host: Host,
    #[cfg(not(target_family = "wasm"))]
    start: std::time::Instant,
}
impl VmInstantiationTimer {
    fn new(_host: Host) -> Self {
        VmInstantiationTimer {
            #[cfg(not(target_family = "wasm"))]
            host: _host,
            #[cfg(not(target_family = "wasm"))]
            start: std::time::Instant::now(),
        }
    }
}
#[cfg(not(target_family = "wasm"))]
impl Drop for VmInstantiationTimer {
    fn drop(&mut self) {
        let _ = self.host.as_budget().track_time(
            ContractCostType::VmInstantiation,
            self.start.elapsed().as_nanos() as u64,
        );
    }
}

/// A [Vm] is a thin wrapper around an instance of [wasmi::Module]. Multiple
/// [Vm]s may be held in a single [Host], and each contains a single WASM module
/// instantiation.
///
/// [Vm] rejects modules with either floating point or start functions.
///
/// [Vm] is configured to use its [Host] as a source of WASM imports.
/// Specifically [Host] implements [wasmi::ImportResolver] by resolving all and
/// only the functions declared in [Env](crate::Env) as imports, if requested by the
/// WASM module. Any other lookups on any tables other than import functions
/// will fail.
pub struct Vm {
    pub(crate) contract_id: ContractId,
    #[allow(dead_code)]
    pub(crate) module: Arc<ParsedModule>,
    #[cfg(feature = "wasmi")]
    wasmi_store: RefCell<wasmi::Store<SendHost>>,
    #[cfg(feature = "wasmi")]
    wasmi_instance: wasmi::Instance,
    #[cfg(feature = "wasmi")]
    pub(crate) wasmi_memory: Option<wasmi::Memory>,

    #[cfg(feature = "wasmtime")]
    wasmtime_store: RefCell<wasmtime::Store<SendHost>>,
    #[cfg(feature = "wasmtime")]
    wasmtime_instance: wasmtime::Instance,
    #[cfg(feature = "wasmtime")]
    pub(crate) wasmtime_memory: Option<wasmtime::Memory>,
}

impl std::hash::Hash for Vm {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.contract_id.hash(state);
    }
}

impl Host {
    // Make a wasmi linker restricted to _only_ importing the symbols
    // mentioned in `symbols`.
    #[cfg(feature = "wasmi")]
    pub(crate) fn make_minimal_wasmi_linker_for_symbols<Ctx: ErrorHandler>(
        context: &Ctx,
        engine: &wasmi::Engine,
        symbols: &BTreeSet<(&str, &str)>,
    ) -> Result<wasmi::Linker<SendHost>, HostError> {
        let mut linker = wasmi::Linker::new(&engine);
        for hf in HOST_FUNCTIONS {
            if symbols.contains(&(hf.mod_str, hf.fn_str)) {
                context
                    .map_err((hf.wrap_wasmi)(&mut linker).map_err(|le| wasmi::Error::Linker(le)))?;
            }
        }
        Ok(linker)
    }

    // Make a wasmi linker that imports all the symbols.
    #[cfg(feature = "wasmi")]
    pub(crate) fn make_maximal_wasmi_linker<Ctx: ErrorHandler>(
        context: &Ctx,
        engine: &wasmi::Engine,
    ) -> Result<wasmi::Linker<SendHost>, HostError> {
        let mut linker = wasmi::Linker::new(&engine);
        for hf in HOST_FUNCTIONS {
            context.map_err((hf.wrap_wasmi)(&mut linker).map_err(|le| wasmi::Error::Linker(le)))?;
        }
        Ok(linker)
    }

    // Make a wasmtime linker restricted to _only_ importing the symbols
    // mentioned in `symbols`.
    #[cfg(feature = "wasmtime")]
    pub(crate) fn make_minimal_wasmtime_linker_for_symbols<Ctx: ErrorHandler>(
        context: &Ctx,
        engine: &wasmtime::Engine,
        symbols: &BTreeSet<(&str, &str)>,
    ) -> Result<wasmtime::Linker<SendHost>, HostError> {
        let mut linker = wasmtime::Linker::new(engine);
        for hf in HOST_FUNCTIONS {
            if symbols.contains(&(hf.mod_str, hf.fn_str)) {
                context.map_wasmtime_error((hf.wrap_wasmtime)(&mut linker))?;
            }
        }
        Ok(linker)
    }

    // Make a wasmtime linker that imports all the symbols.
    #[cfg(feature = "wasmtime")]
    pub(crate) fn make_maximal_wasmtime_linker<Ctx: ErrorHandler>(
        context: &Ctx,
        engine: &wasmtime::Engine,
    ) -> Result<wasmtime::Linker<SendHost>, HostError> {
        let mut linker = wasmtime::Linker::new(engine);
        for hf in HOST_FUNCTIONS {
            context.map_wasmtime_error((hf.wrap_wasmtime)(&mut linker))?;
        }
        Ok(linker)
    }
}

impl Vm {
    /// The maximum number of arguments that can be passed to a VM function.
    pub const MAX_VM_ARGS: usize = 32;

    #[cfg(feature = "testutils")]
    pub fn get_all_host_functions() -> Vec<(&'static str, &'static str, u32)> {
        HOST_FUNCTIONS
            .iter()
            .map(|hf| (hf.mod_str, hf.fn_str, hf.arity))
            .collect()
    }

    #[cfg(feature = "testutils")]
    #[allow(clippy::type_complexity)]
    pub fn get_all_host_functions_with_supported_protocol_range(
    ) -> Vec<(&'static str, &'static str, u32, Option<u32>, Option<u32>)> {
        HOST_FUNCTIONS
            .iter()
            .map(|hf| (hf.mod_str, hf.fn_str, hf.arity, hf.min_proto, hf.max_proto))
            .collect()
    }

    /// Instantiate wasmi components specifically (vs. any other future backend).
    #[cfg(feature = "wasmi")]
    fn instantiate_wasmi(
        host: &Host,
        parsed_module: &Arc<ParsedModule>,
        wasmi_linker: &wasmi::Linker<SendHost>,
    ) -> Result<
        (
            wasmi::Store<SendHost>,
            wasmi::Instance,
            Option<wasmi::Memory>,
        ),
        HostError,
    > {
        let _span = tracy_span!("Vm::instantiate_wasmi");

        let wasmi_engine = parsed_module.wasmi_module.engine();
        let mut store = {
            let _span = tracy_span!("Vm::instantiate_wasmi - store");
            wasmi::Store::new(wasmi_engine, SendHost(host.clone()))
        };
        parsed_module.cost_inputs.charge_for_instantiation(host)?;
        store.limiter(|host| host);
        parsed_module.check_contract_imports_match_host_protocol(host)?;
        let not_started_instance = {
            let _span = tracy_span!("Vm::instantiate_wasmi - instantiate");
            host.map_err(wasmi_linker.instantiate(&mut store, &parsed_module.wasmi_module))?
        };

        let instance = host.map_err(
            not_started_instance
                .ensure_no_start(&mut store)
                .map_err(|ie| wasmi::Error::Instantiation(ie)),
        )?;

        let memory = if let Some(ext) = instance.get_export(&mut store, "memory") {
            ext.into_memory()
        } else {
            None
        };
        Ok((store, instance, memory))
    }

    #[cfg(feature = "wasmtime")]
    fn instantiate_wasmtime(
        host: &Host,
        parsed_module: &Arc<ParsedModule>,
        wasmtime_linker: &wasmtime::Linker<SendHost>,
    ) -> Result<
        (
            wasmtime::Store<SendHost>,
            wasmtime::Instance,
            Option<wasmtime::Memory>,
        ),
        HostError,
    > {
        let _span = tracy_span!("Vm::instantiate_wasmtime");

        let wasmtime_engine = parsed_module.wasmtime_module.engine();
        let mut wasmtime_store = {
            let _span = tracy_span!("Vm::instantiate_wasmtime - store");
            wasmtime::Store::new(&wasmtime_engine, SendHost(host.clone()))
        };
        parsed_module.cost_inputs.charge_for_instantiation(host)?;
        wasmtime_store.limiter(|host| host);
        parsed_module.check_contract_imports_match_host_protocol(host)?;
        let wasmtime_instance = {
            let _span = tracy_span!("Vm::instantiate_wasmtime - instantiate");
            host.map_wasmtime_error(
                wasmtime_linker.instantiate(&mut wasmtime_store, &parsed_module.wasmtime_module),
            )?
        };
        let wasmtime_memory =
            if let Some(ext) = wasmtime_instance.get_export(&mut wasmtime_store, "memory") {
                ext.into_memory()
            } else {
                None
            };
        Ok((wasmtime_store, wasmtime_instance, wasmtime_memory))
    }

    /// Instantiates a VM given the arguments provided in [`Self::new`],
    /// or [`Self::new_from_module_cache`]
    fn instantiate(
        host: &Host,
        contract_id: ContractId,
        parsed_module: Arc<ParsedModule>,
        #[cfg(feature = "wasmi")] wasmi_linker: &wasmi::Linker<SendHost>,
        #[cfg(feature = "wasmtime")] wasmtime_linker: &wasmtime::Linker<SendHost>,
    ) -> Result<Rc<Self>, HostError> {
        let _span = tracy_span!("Vm::instantiate");

        // The host really never should have made it past construction on an old
        // protocol version, but it doesn't hurt to double check here before we
        // instantiate a VM, which is the place old-protocol replay will
        // diverge.
        host.check_ledger_protocol_supported()?;

        #[cfg(feature = "wasmi")]
        let (wasmi_store, wasmi_instance, wasmi_memory) =
            Self::instantiate_wasmi(host, &parsed_module, wasmi_linker)?;

        #[cfg(feature = "wasmtime")]
        let (wasmtime_store, wasmtime_instance, wasmtime_memory) =
            Self::instantiate_wasmtime(host, &parsed_module, wasmtime_linker)?;

        // Here we do _not_ supply the store with any fuel. Fuel is supplied
        // right before the VM is being run, i.e., before crossing the host->VM
        // boundary.
        Ok(Rc::new(Self {
            contract_id,
            module: parsed_module,
            #[cfg(feature = "wasmi")]
            wasmi_store: RefCell::new(wasmi_store),
            #[cfg(feature = "wasmi")]
            wasmi_instance,
            #[cfg(feature = "wasmi")]
            wasmi_memory,
            #[cfg(feature = "wasmtime")]
            wasmtime_store: RefCell::new(wasmtime_store),
            #[cfg(feature = "wasmtime")]
            wasmtime_instance,
            #[cfg(feature = "wasmtime")]
            wasmtime_memory,
        }))
    }

    pub fn from_parsed_module(
        host: &Host,
        contract_id: ContractId,
        parsed_module: Arc<ParsedModule>,
    ) -> Result<Rc<Self>, HostError> {
        let _span = tracy_span!("Vm::from_parsed_module");
        VmInstantiationTimer::new(host.clone());
        if let Some(cache) = &*host.try_borrow_module_cache()? {
            Self::instantiate(
                host,
                contract_id,
                parsed_module,
                #[cfg(feature = "wasmi")]
                &cache.wasmi_linker,
                #[cfg(feature = "wasmtime")]
                &cache.wasmtime_linker,
            )
        } else {
            #[cfg(feature = "wasmi")]
            let wasmi_linker = parsed_module.make_wasmi_linker(host)?;
            #[cfg(feature = "wasmtime")]
            let wasmtime_linker = parsed_module.make_wasmtime_linker(host)?;
            Self::instantiate(
                host,
                contract_id,
                parsed_module,
                #[cfg(feature = "wasmi")]
                &wasmi_linker,
                #[cfg(feature = "wasmtime")]
                &wasmtime_linker,
            )
        }
    }

    /// Constructs a new instance of a [Vm] within the provided [Host],
    /// establishing a new execution context for a contract identified by
    /// `contract_id` with Wasm bytecode provided in `module_wasm_code`.
    ///
    /// This function performs several steps:
    ///
    ///   - Parses and performs Wasm validation on the module.
    ///   - Checks that the module contains an [meta::INTERFACE_VERSION] that
    ///     matches the host.
    ///   - Checks that the module has no floating point code or `start`
    ///     function, or post-MVP wasm extensions.
    ///   - Instantiates the module, leaving it ready to accept function
    ///     invocations.
    ///   - Looks up and caches its linear memory export named `memory`
    ///     if it exists.
    ///
    /// With the introduction of the granular cost inputs this method
    /// should only be used for the one-off full parses of the new Wasms
    /// during the initial upload verification.
    pub fn new(host: &Host, contract_id: ContractId, wasm: &[u8]) -> Result<Rc<Self>, HostError> {
        let cost_inputs = VersionedContractCodeCostInputs::V0 {
            wasm_bytes: wasm.len(),
        };
        Self::new_with_cost_inputs(host, contract_id, wasm, cost_inputs)
    }

    pub(crate) fn new_with_cost_inputs(
        host: &Host,
        contract_id: ContractId,
        wasm: &[u8],
        cost_inputs: VersionedContractCodeCostInputs,
    ) -> Result<Rc<Self>, HostError> {
        let _span = tracy_span!("Vm::new");
        VmInstantiationTimer::new(host.clone());
        let parsed_module = ParsedModule::new_with_isolated_engine(host, wasm, cost_inputs)?;
        #[cfg(feature = "wasmi")]
        let wasmi_linker = parsed_module.make_wasmi_linker(host)?;
        #[cfg(feature = "wasmtime")]
        let wasmtime_linker = parsed_module.make_wasmtime_linker(host)?;
        Self::instantiate(
            host,
            contract_id,
            parsed_module,
            #[cfg(feature = "wasmi")]
            &wasmi_linker,
            #[cfg(feature = "wasmtime")]
            &wasmtime_linker,
        )
    }

    #[cfg(feature = "wasmi")]
    pub(crate) fn get_wasmi_memory(&self, host: &Host) -> Result<wasmi::Memory, HostError> {
        match self.wasmi_memory {
            Some(mem) => Ok(mem),
            None => Err(host.err(
                ScErrorType::WasmVm,
                ScErrorCode::MissingValue,
                "no linear memory named `memory`",
                &[],
            )),
        }
    }

    #[cfg(feature = "wasmtime")]
    pub(crate) fn get_wasmtime_memory(&self, host: &Host) -> Result<wasmtime::Memory, HostError> {
        match self.wasmtime_memory {
            Some(mem) => Ok(mem),
            None => Err(host.err(
                ScErrorType::WasmVm,
                ScErrorCode::MissingValue,
                "no linear memory named `memory`",
                &[],
            )),
        }
    }

    // Wrapper for the [`Func`] call which is metered as a component.
    // Resolves the function entity, and takes care the conversion between and
    // tranfering of the host budget / VM fuel. This is where the host->VM->host
    // boundaries are crossed.
    #[cfg(feature = "wasmi")]
    pub(crate) fn metered_wasmi_func_call(
        self: &Rc<Self>,
        host: &Host,
        func_sym: &Symbol,
        inputs: &[wasmi::Value],
        treat_missing_function_as_noop: bool,
    ) -> Result<Val, HostError> {
        host.charge_budget(ContractCostType::InvokeVmFunction, None)?;

        // resolve the function entity to be called
        let func_ss: SymbolStr = func_sym.try_into_val(host)?;
        let ext = match self
            .wasmi_instance
            .get_export(&*self.wasmi_store.try_borrow_or_err()?, func_ss.as_ref())
        {
            None => {
                if treat_missing_function_as_noop {
                    return Ok(Val::VOID.into());
                } else {
                    return Err(host.err(
                        ScErrorType::WasmVm,
                        ScErrorCode::MissingValue,
                        "trying to invoke non-existent contract function",
                        &[func_sym.to_val()],
                    ));
                }
            }
            Some(e) => e,
        };
        let func = match ext.into_func() {
            None => {
                return Err(host.err(
                    ScErrorType::WasmVm,
                    ScErrorCode::UnexpectedType,
                    "trying to invoke Wasm export that is not a function",
                    &[func_sym.to_val()],
                ))
            }
            Some(e) => e,
        };

        if inputs.len() > Vm::MAX_VM_ARGS {
            return Err(host.err(
                ScErrorType::WasmVm,
                ScErrorCode::InvalidInput,
                "Too many arguments in Wasm invocation",
                &[func_sym.to_val()],
            ));
        }

        // call the function
        let mut wasm_ret: [wasmi::Value; 1] = [wasmi::Value::I64(0)];
        let added_fuel = self
            .wasmi_store
            .try_borrow_mut_or_err()?
            .add_fuel_to_vm(host)?;
        host.save_last_vm_fuel(added_fuel)?;

        // Metering: the `func.call` will trigger `wasmi::Call` (or `CallIndirect`) instruction,
        // which is technically covered by wasmi fuel metering. So we are double charging a bit
        // here (by a few 100s cpu insns). It is better to be safe.
        let res = func.call(
            &mut *self.wasmi_store.try_borrow_mut_or_err()?,
            inputs,
            &mut wasm_ret,
        );
        // Due to the way wasmi's fuel metering works (it does `remaining.checked_sub(delta).ok_or(Trap)`),
        // there may be a small amount of fuel (less than delta -- the fuel cost of that failing
        // wasmi instruction) remaining when the `OutOfFuel` trap occurs. This is only observable
        // if the contract traps with `OutOfFuel`, which may appear confusing if they look closely
        // at the budget amount consumed. So it should be fine.
        let last_fuel = host.take_last_vm_fuel()?;
        self.wasmi_store
            .try_borrow_mut_or_err()?
            .return_fuel_to_host(host, last_fuel)?;

        if let Err(e) = res {
            use std::borrow::Cow;

            // When a call fails with a wasmi::Error::Trap that carries a HostError
            // we propagate that HostError as is, rather than producing something new.

            match e {
                wasmi::Error::Trap(trap) => {
                    if let Some(code) = trap.trap_code() {
                        let err = code.into();
                        let mut msg = Cow::Borrowed("VM call trapped");
                        host.with_debug_mode(|| {
                            msg = Cow::Owned(format!("VM call trapped: {:?}", &code));
                            Ok(())
                        });
                        return Err(host.error(err, &msg, &[func_sym.to_val()]));
                    }
                    if let Some(he) = trap.downcast::<HostError>() {
                        host.log_diagnostics(
                            "VM call trapped with HostError",
                            &[func_sym.to_val(), he.error.to_val()],
                        );
                        return Err(he);
                    }
                    return Err(host.err(
                        ScErrorType::WasmVm,
                        ScErrorCode::InternalError,
                        "VM trapped but propagation failed",
                        &[],
                    ));
                }
                e => {
                    let mut msg = Cow::Borrowed("VM call failed");
                    host.with_debug_mode(|| {
                        msg = Cow::Owned(format!("VM call failed: {:?}", &e));
                        Ok(())
                    });
                    return Err(host.error(e.into(), &msg, &[func_sym.to_val()]));
                }
            }
        }
        host.relative_to_absolute(
            Val::try_marshal_from_value(wasm_ret[0].clone()).ok_or(ConversionError)?,
        )
    }

    #[cfg(feature = "wasmtime")]
    pub(crate) fn metered_wasmtime_func_call(
        self: &Rc<Self>,
        host: &Host,
        func_sym: &Symbol,
        inputs: &[wasmtime::Val],
        treat_missing_function_as_noop: bool,
    ) -> Result<Val, HostError> {
        let _span = tracy_span!("Vm::metered_wasmtime_func_call");

        host.charge_budget(ContractCostType::InvokeVmFunction, None)?;

        // resolve the function entity to be called
        let func_ss: SymbolStr = func_sym.try_into_val(host)?;
        let ext = match self.wasmtime_instance.get_export(
            &mut *self.wasmtime_store.try_borrow_mut_or_err()?,
            func_ss.as_ref(),
        ) {
            None => {
                if treat_missing_function_as_noop {
                    return Ok(Val::VOID.into());
                } else {
                    return Err(host.err(
                        ScErrorType::WasmVm,
                        ScErrorCode::MissingValue,
                        "trying to invoke non-existent contract function",
                        &[func_sym.to_val()],
                    ));
                }
            }
            Some(e) => e,
        };
        let func = match ext.into_func() {
            None => {
                return Err(host.err(
                    ScErrorType::WasmVm,
                    ScErrorCode::UnexpectedType,
                    "trying to invoke Wasm export that is not a function",
                    &[func_sym.to_val()],
                ))
            }
            Some(e) => e,
        };

        if inputs.len() > Vm::MAX_VM_ARGS {
            return Err(host.err(
                ScErrorType::WasmVm,
                ScErrorCode::InvalidInput,
                "Too many arguments in Wasm invocation",
                &[func_sym.to_val()],
            ));
        }

        // call the function
        let mut wasm_ret: [wasmtime::Val; 1] = [wasmtime::Val::I64(0)];
        let added_fuel = self
            .wasmtime_store
            .try_borrow_mut_or_err()?
            .add_fuel_to_vm(host)?;
        host.save_last_vm_fuel(added_fuel)?;

        let res = {
            let _span = tracy_span!("Vm::metered_wasmtime_func_call - actual call");
            func.call(
                &mut *self.wasmtime_store.try_borrow_mut_or_err()?,
                inputs,
                &mut wasm_ret,
            )
        };

        let last_fuel = host.take_last_vm_fuel()?;
        self.wasmtime_store
            .try_borrow_mut_or_err()?
            .return_fuel_to_host(host, last_fuel)?;

        if let Err(e) = res {
            // FIXME: this needs to be fairly careful about correct propagation.
            // currently we're just doing a crude downcast attempt.
            return host.map_wasmtime_error(Err(e));
        }
        host.relative_to_absolute(
            Val::try_marshal_from_wasmtime_value(wasm_ret[0]).ok_or(ConversionError)?,
        )
    }

    // FIXME: remove when/if we decide to commit to this transition.
    pub(crate) const FIRST_PROTOCOL_TO_RUN_ON_WASMTIME: u32 = 21;

    pub(crate) fn invoke_function_raw(
        self: &Rc<Self>,
        host: &Host,
        func_sym: &Symbol,
        args: &[Val],
        treat_missing_function_as_noop: bool,
    ) -> Result<Val, HostError> {
        let _span = tracy_span!("Vm::invoke_function_raw");
        if host.is_wasmtime()? {
            #[cfg(feature = "wasmtime")]
            {
                Vec::<wasmtime::Val>::charge_bulk_init_cpy(args.len() as u64, host.as_budget())?;
                let wasmtime_args: Vec<wasmtime::Val> = args
                    .iter()
                    .map(|i| {
                        host.absolute_to_relative(*i)
                            .map(|v| v.marshal_wasmtime_from_self())
                    })
                    .collect::<Result<Vec<wasmtime::Val>, HostError>>()?;
                return self.metered_wasmtime_func_call(
                    host,
                    func_sym,
                    wasmtime_args.as_slice(),
                    treat_missing_function_as_noop,
                );
            }
            #[cfg(not(feature = "wasmtime"))]
            {
                return Err(host.err(
                    ScErrorType::WasmVm,
                    ScErrorCode::InternalError,
                    "wasmtime support not compiled in",
                    &[],
                ));
            }
        } else {
            #[cfg(feature = "wasmi")]
            {
                Vec::<wasmi::Value>::charge_bulk_init_cpy(args.len() as u64, host.as_budget())?;
                let wasm_args: Vec<wasmi::Value> = args
                    .iter()
                    .map(|i| host.absolute_to_relative(*i).map(|v| v.marshal_from_self()))
                    .collect::<Result<Vec<wasmi::Value>, HostError>>()?;
                return self.metered_wasmi_func_call(
                    host,
                    func_sym,
                    wasm_args.as_slice(),
                    treat_missing_function_as_noop,
                );
            }
            #[cfg(not(feature = "wasmi"))]
            {
                return Err(host.err(
                    ScErrorType::WasmVm,
                    ScErrorCode::InternalError,
                    "wasmi support not compiled in",
                    &[],
                ));
            }
        }
    }

    #[cfg(feature = "wasmi")]
    pub(crate) fn with_vmcontext<F, T>(&self, f: F) -> Result<T, HostError>
    where
        F: for<'a> FnOnce(VmContext<'a, SendHost>) -> Result<T, HostError>,
    {
        if let Ok(mut store) = self.wasmi_store.try_borrow_mut_or_err() {
            let ctx: wasmi::StoreContextMut<'_, SendHost> = (&mut *store).into();
            f(ctx.into())
        } else {
            f(VmContext::AlreadyBorrowedVm)
        }
    }

    #[cfg(feature = "wasmtime")]
    pub(crate) fn with_vmcontext<F, T>(&self, f: F) -> Result<T, HostError>
    where
        F: for<'a> FnOnce(VmContext<'a, SendHost>) -> Result<T, HostError>,
    {
        if let Ok(mut store) = self.wasmtime_store.try_borrow_mut_or_err() {
            f((&mut *store).as_context_mut().into())
        } else {
            f(VmContext::AlreadyBorrowedVm)
        }
    }

    #[cfg(feature = "wasmi")]
    pub(crate) fn memory_hash_and_size(
        &self,
        budget: &Budget,
        mut vmctx: VmContext<'_, SendHost>,
    ) -> Result<(u64, usize), HostError> {
        use std::hash::Hasher;
        if let (Some(mem), VmContext::Wasmi(wasmictx)) = (self.wasmi_memory, vmctx) {
            let mut state = CountingHasher::default();
            let data = mem.data(&wasmictx);
            data.metered_hash(&mut state, budget)?;
            Ok((state.finish(), data.len()))
        } else {
            Ok((0, 0))
        }
    }

    #[cfg(all(feature = "wasmtime", not(feature = "wasmi")))]
    pub(crate) fn memory_hash_and_size(
        &self,
        budget: &Budget,
        vmctx: VmContext<'_, SendHost>,
    ) -> Result<(u64, usize), HostError> {
        use std::hash::Hasher;
        if let (Some(mem), VmContext::Wasmtime(wasmtimectx)) = (self.wasmtime_memory, vmctx) {
            let mut state = CountingHasher::default();
            let data = mem.data(wasmtimectx);
            data.metered_hash(&mut state, budget)?;
            Ok((state.finish(), data.len()))
        } else {
            return Ok((0, 0));
        }
    }

    // This is pretty weak: we just observe the state that wasmi exposes through
    // wasm _exports_. There might be tables or globals a wasm doesn't export
    // but there's no obvious way to observe them.
    #[cfg(feature = "wasmi")]
    pub(crate) fn exports_hash_and_size(
        &self,
        budget: &Budget,
        mut vmctx: VmContext<'_, SendHost>,
    ) -> Result<(u64, usize), HostError> {
        use std::hash::Hasher;
        use wasmi::Extern;
        let VmContext::Wasmi(wasmictx) = vmctx else {
            return Ok((0, 0));
        };
        let mut size: usize = 0;
        let mut state = CountingHasher::default();
        for export in self.wasmi_instance.exports(&wasmictx) {
            size = size.saturating_add(1);
            export.name().metered_hash(&mut state, budget)?;

            match export.into_extern() {
                // Funcs are immutable, memory we hash separately above.
                Extern::Func(_) | Extern::Memory(_) => (),

                Extern::Table(t) => {
                    let sz = t.size(&wasmictx);
                    sz.metered_hash(&mut state, budget)?;
                    size = size.saturating_add(sz as usize);
                    for i in 0..sz {
                        if let Some(elem) = t.get(&wasmictx, i) {
                            // This is a slight fudge to avoid having to
                            // define a ton of additional MeteredHash impls
                            // for wasmi substructures, since there is a
                            // bounded size on the string representation of
                            // a value, we're comfortable going temporarily
                            // over budget here.
                            let s = format!("{:?}", elem);
                            budget.charge(ContractCostType::MemAlloc, Some(s.len() as u64))?;
                            s.metered_hash(&mut state, budget)?;
                        }
                    }
                }
                Extern::Global(g) => {
                    let s = format!("{:?}", g.get(&wasmictx));
                    budget.charge(ContractCostType::MemAlloc, Some(s.len() as u64))?;
                    s.metered_hash(&mut state, budget)?;
                }
            }
        }
        Ok((state.finish(), size))
    }

    #[cfg(all(feature = "wasmtime", not(feature = "wasmi")))]
    pub(crate) fn exports_hash_and_size(
        &self,
        budget: &Budget,
        vmctx: VmContext<'_, SendHost>,
    ) -> Result<(u64, usize), HostError> {
        use std::hash::Hasher;
        use wasmtime::Extern;
        let VmContext::Wasmtime(mut wasmtimectx) = vmctx else {
            return Ok((0, 0));
        };
        let mut size: usize = 0;
        let mut state = CountingHasher::default();
        let externs: Vec<(String, wasmtime::Extern)> = {
            self.wasmtime_instance
                .exports(&mut wasmtimectx)
                .map(|export| (export.name().to_string(), export.into_extern()))
                .collect()
        };
        for (name, xtern) in externs {
            size = size.saturating_add(1);
            name.metered_hash(&mut state, budget)?;
            match xtern {
                Extern::Func(_) | Extern::Memory(_) | Extern::SharedMemory(_) | Extern::Tag(_) => {
                    ()
                }

                Extern::Table(t) => {
                    let sz = t.size(&mut wasmtimectx);
                    sz.metered_hash(&mut state, budget)?;
                    size = size.saturating_add(sz as usize);
                    for i in 0..sz {
                        if let Some(elem) = t.get(&mut wasmtimectx, i) {
                            // This is a slight fudge to avoid having to
                            // define a ton of additional MeteredHash impls
                            // for wasmtime substructures, since there is a
                            // bounded size on the string representation of
                            // a value, we're comfortable going temporarily
                            // over budget here.
                            let s = format!("{:?}", elem);
                            budget.charge(ContractCostType::MemAlloc, Some(s.len() as u64))?;
                            s.metered_hash(&mut state, budget)?;
                        }
                    }
                }
                Extern::Global(g) => {
                    let s = format!("{:?}", g.get(&mut wasmtimectx));
                    budget.charge(ContractCostType::MemAlloc, Some(s.len() as u64))?;
                    s.metered_hash(&mut state, budget)?;
                }
            }
        }
        Ok((state.finish(), size))
    }
}
