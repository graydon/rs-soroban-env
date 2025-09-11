use crate::{
    budget::{AsBudget, Budget},
    xdr::ContractCostType,
    HostError,
};

pub(crate) struct WasmtimeLimits {
    pub table_elements: usize,
}

pub(crate) const WASMTIME_LIMITS_CONFIG: WasmtimeLimits = WasmtimeLimits {
    table_elements: 1000,
};

impl wasmtime::ResourceLimiter for crate::Host {
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
        .consume_fuel(true)
        .wasm_bulk_memory(true)
        .wasm_multi_value(false)
        .wasm_simd(false)
        .wasm_tail_call(false);
    Ok(config)
}
