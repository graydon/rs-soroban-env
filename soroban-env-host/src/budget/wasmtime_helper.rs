use wasmtime::wasmparser::WasmFeatures;

use crate::{
    budget::{AsBudget, Budget},
    vm::SendHost,
    xdr::ContractCostType,
    HostError,
};

pub(crate) struct WasmtimeLimits {
    pub table_elements: usize,
}

pub(crate) const WASMTIME_LIMITS_CONFIG: WasmtimeLimits = WasmtimeLimits {
    table_elements: 1000,
};

impl wasmtime::ResourceLimiter for SendHost {
    fn memory_growing(
        &mut self,
        current: usize,
        desired: usize,
        maximum: Option<usize>,
    ) -> wasmtime::Result<bool> {
        let host_limit = self
            .as_budget()
            .get_mem_bytes_remaining()
            .map_err(|e| wasmtime::Error::from(HostError::from(e)))?;

        let delta = (desired as u64).saturating_sub(current as u64);
        let allow = if delta > host_limit {
            false
        } else {
            match maximum {
                Some(max) => desired <= max,
                None => true,
            }
        };

        if allow {
            #[cfg(any(test, feature = "testutils", feature = "bench"))]
            {
                self.as_budget()
                    .track_wasm_mem_alloc(delta)
                    .map_err(|e| wasmtime::Error::from(HostError::from(e)))?;
            }

            self.as_budget()
                .charge(ContractCostType::MemAlloc, Some(delta))
                .map(|_| true)
                .map_err(|e| wasmtime::Error::from(HostError::from(e)))
        } else {
            Err(wasmtime::Error::from(wasmtime::Trap::AllocationTooLarge))
        }
    }

    fn table_growing(
        &mut self,
        _current: usize,
        desired: usize,
        maximum: Option<usize>,
    ) -> wasmtime::Result<bool> {
        let allow = if desired > WASMTIME_LIMITS_CONFIG.table_elements {
            false
        } else {
            match maximum {
                Some(max) => desired <= max,
                None => true,
            }
        };
        if allow {
            Ok(allow)
        } else {
            Err(wasmtime::Error::from(wasmtime::Trap::AllocationTooLarge))
        }
    }
}

pub(crate) fn get_wasmtime_config(_budget: &Budget) -> Result<wasmtime::Config, HostError> {
    let mut config = wasmtime::Config::new();
    config
        .strategy(wasmtime::Strategy::Winch)
        .debug_info(false)
        .generate_address_map(false)
        // Stuff we had enabled-or-disabled on wasmi.
        .consume_fuel(true)
        .wasm_bulk_memory(true)
        .wasm_features(WasmFeatures::MUTABLE_GLOBAL, true)
        .wasm_features(WasmFeatures::SIGN_EXTENSION, true)
        .wasm_features(WasmFeatures::SATURATING_FLOAT_TO_INT, false)
        .wasm_multi_value(false)
        .wasm_features(WasmFeatures::REFERENCE_TYPES, false)
        .wasm_tail_call(false)
        .wasm_extended_const(false)
        .wasm_features(WasmFeatures::FLOATS, false)
        // Disable some more stuff while we're here, just to be sure.
        .wasm_simd(false)
        .wasm_relaxed_simd(false)
        .wasm_features(WasmFeatures::THREADS, false)
        .wasm_shared_everything_threads(false)
        .wasm_multi_memory(false)
        .wasm_features(WasmFeatures::EXCEPTIONS, false)
        .wasm_memory64(false)
        .wasm_features(WasmFeatures::COMPONENT_MODEL, false)
        .wasm_features(WasmFeatures::FUNCTION_REFERENCES, false)
        .wasm_features(WasmFeatures::MEMORY_CONTROL, false)
        .wasm_features(WasmFeatures::GC, false)
        .wasm_features(WasmFeatures::CUSTOM_PAGE_SIZES, false)
        .wasm_features(WasmFeatures::LEGACY_EXCEPTIONS, false)
        .wasm_features(WasmFeatures::GC_TYPES, false)
        .wasm_features(WasmFeatures::STACK_SWITCHING, false)
        .wasm_features(WasmFeatures::WIDE_ARITHMETIC, false)
        .wasm_features(WasmFeatures::CM_VALUES, false)
        .wasm_features(WasmFeatures::CM_NESTED_NAMES, false)
        .wasm_features(WasmFeatures::CM_ASYNC, false)
        .wasm_features(WasmFeatures::CM_ASYNC_STACKFUL, false)
        .wasm_features(WasmFeatures::CM_ASYNC_BUILTINS, false)
        .wasm_features(WasmFeatures::CM_THREADING, false)
        .wasm_features(WasmFeatures::CM_ERROR_CONTEXT, false)
        .wasm_features(WasmFeatures::CM_FIXED_SIZE_LIST, false)
        .wasm_features(WasmFeatures::CM_GC, false)
        .wasm_features(WasmFeatures::CALL_INDIRECT_OVERLONG, false);

    Ok(config)
}
