use super::{
    func_info::HOST_FUNCTIONS,
    get_wasmtime_config,
    parsed_module::{ParsedModule, VersionedContractCodeCostInputs},
};
use crate::{
    budget::{get_wasmi_config, AsBudget, Budget},
    host::metered_clone::{MeteredClone, MeteredContainer},
    xdr::{Hash, ScErrorCode, ScErrorType},
    Host, HostError, MeteredOrdMap,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
    sync::{Arc, Mutex, MutexGuard},
};
use wasmi::{Engine, Linker};

/// A [ModuleCache] is a cache of a set of Wasm modules that have been parsed
/// but not yet instantiated, along with a shared and reusable [Engine] storing
/// their code. The cache must be populated eagerly with all the contracts in a
/// single [Host]'s lifecycle (at least) added all at once, since each wasmi
/// [Engine] is locked during execution and no new modules can be added to it.
#[derive(Clone, Default)]
pub struct ModuleCache {
    pub(crate) engine: Engine,
    pub(crate) wasmtime_engine: wasmtime::Engine,
    pub(crate) linker: Linker<Host>,
    pub(crate) wasmtime_linker: wasmtime::Linker<Host>,
    modules: ModuleCacheMap,
}

// The module cache was originally designed as an immutable object
// established at host creation time and never updated. In order to support
// longer-lived modules caches, we allow construction of unmetered, "reusable"
// module maps, that imply various changes:
//
// - Modules can be added post-construction.
// - Adding an existing module is a harmless no-op, not an error.
// - The linkers are set to "maximal" mode to cover all possible imports.
// - Randomized cache-trimming is enabled.
// - The cache easily scales to a large number of modules, unlike MeteredOrdMap.
// - There is no metering of cache map operations.
// - The cache can be cloned, but the clone is a shallow copy.
// - The cache is mutable and shared among all copies, using a mutex.

#[derive(Clone)]
enum ModuleCacheMap {
    MeteredSingleUseMap(MeteredOrdMap<Hash, Rc<ParsedModule>, Budget>),
    UnmeteredReusableMap(Arc<Mutex<BTreeMap<Hash, Rc<ParsedModule>>>>),
}

impl Default for ModuleCacheMap {
    fn default() -> Self {
        Self::MeteredSingleUseMap(MeteredOrdMap::new())
    }
}

impl ModuleCacheMap {
    fn lock_map(
        map: &Arc<Mutex<BTreeMap<Hash, Rc<ParsedModule>>>>,
    ) -> Result<MutexGuard<BTreeMap<Hash, Rc<ParsedModule>>>, HostError> {
        map.lock()
            .map_err(|_| HostError::from((ScErrorType::Context, ScErrorCode::InternalError)))
    }

    fn is_reusable(&self) -> bool {
        matches!(self, Self::UnmeteredReusableMap(_))
    }

    fn contains_key(&self, key: &Hash, budget: &Budget) -> Result<bool, HostError> {
        match self {
            Self::MeteredSingleUseMap(map) => map.contains_key(key, budget),
            Self::UnmeteredReusableMap(map) => Ok(Self::lock_map(map)?.contains_key(key)),
        }
    }

    fn get(&self, key: &Hash, budget: &Budget) -> Result<Option<Rc<ParsedModule>>, HostError> {
        match self {
            Self::MeteredSingleUseMap(map) => Ok(map.get(key, budget)?.map(|rc| rc.clone())),
            Self::UnmeteredReusableMap(map) => {
                Ok(Self::lock_map(map)?.get(key).map(|rc| rc.clone()))
            }
        }
    }

    fn insert(
        &mut self,
        key: Hash,
        value: Rc<ParsedModule>,
        budget: &Budget,
    ) -> Result<(), HostError> {
        match self {
            Self::MeteredSingleUseMap(map) => {
                *map = map.insert(key, value, budget)?;
            }
            Self::UnmeteredReusableMap(map) => {
                Self::lock_map(map)?.insert(key, value);
            }
        }
        Ok(())
    }
}

impl ModuleCache {
    pub fn new(host: &Host) -> Result<Self, HostError> {
        let config = get_wasmi_config(host.as_budget())?;
        let engine = Engine::new(&config);

        let wasmtime_config = get_wasmtime_config(host.as_budget())?;
        let wasmtime_engine = host.map_wasmtime_error(wasmtime::Engine::new(&wasmtime_config))?;

        let modules = ModuleCacheMap::MeteredSingleUseMap(MeteredOrdMap::new());
        let linker = wasmi::Linker::new(&engine);
        let wasmtime_linker = wasmtime::Linker::new(&wasmtime_engine);
        let mut cache = Self {
            engine,
            wasmtime_engine,
            modules,
            linker,
            wasmtime_linker,
        };
        cache.add_stored_contracts(host)?;
        Ok(cache)
    }

    pub fn new_reusable(host: &Host) -> Result<Self, HostError> {
        let mut cache = Self::new(host)?;
        cache.modules = ModuleCacheMap::UnmeteredReusableMap(Arc::new(Mutex::new(BTreeMap::new())));
        cache.set_linkers_to_maximal(host)?;
        Ok(cache)
    }

    // Set the linkers in the module cache to allow all possible symbols, which
    // is usually the setting you want when using a module cache incrementally.
    pub fn set_linkers_to_maximal(&mut self, host: &Host) -> Result<(), HostError> {
        if !self.modules.is_reusable() {
            return Err(host.err(
                ScErrorType::Context,
                ScErrorCode::InternalError,
                "set_linkers_to_maximal called on non-reusable cache",
                &[],
            ));
        }
        self.linker = Host::make_maximal_linker(&self.engine)?;
        self.wasmtime_linker = Host::make_maximal_wasmtime_linker(host, &self.wasmtime_engine)?;
        Ok(())
    }

    // Using the host's attached PRNG, randomly trim elements from the cache
    // until it's the given size.
    pub fn randomly_trim_to_max_size(&mut self, host: &Host, sz: usize) -> Result<(), HostError> {
        let ModuleCacheMap::UnmeteredReusableMap(modules) = &mut self.modules else {
            return Err(host.err(
                ScErrorType::Context,
                ScErrorCode::InternalError,
                "randomly_trim_to_max_size called on non-UnmeteredReusableMap cache",
                &[],
            ));
        };
        let mut modules = ModuleCacheMap::lock_map(modules)?;
        if sz == 0 {
            modules.clear();
        } else {
            if modules.len() > sz {
                let Some(prng) = &mut *host.try_borrow_base_prng_mut()? else {
                    return Err(host.err(
                        ScErrorType::Context,
                        ScErrorCode::InternalError,
                        "no base PRNG available",
                        &[],
                    ));
                };

                // If we draw a uniform random value in 0..n, and we do this n
                // times, we expect to draw each value in that range about once.
                // The number of those draws that are less than some number sz
                // should be about the same magnitude as sz. This is slightly
                // noisy so we do it in an outer while loop, but the expected
                // number of iterations is 1 or 2.
                //
                // If the budget runs out, it will over-trim the cache (the
                // predicate returns true on everything) which will at least
                // exit the loop quickly. But you should try not to run out of
                // budget; this is intended to be run in the unmetered case on a
                // host that is a fake-host with an infinite budget.
                while modules.len() > sz {
                    let n = modules.len() as u64 - 1;
                    modules.retain(|_, _| {
                        prng.u64_in_inclusive_range(0..=n, host.as_budget())
                            .unwrap_or_default()
                            < sz as u64
                    });
                }
            }
        }
        Ok(())
    }

    pub fn add_stored_contracts(&mut self, host: &Host) -> Result<(), HostError> {
        use crate::xdr::{ContractCodeEntry, ContractCodeEntryExt, LedgerEntryData, LedgerKey};
        let storage = host.try_borrow_storage()?;
        for (k, v) in storage.map.iter(host.as_budget())? {
            // In recording mode we build the module cache *after* the contract invocation has
            // finished. This means that if any new Wasm has been uploaded, then we will add it to
            // the cache. However, in the 'real' flow we build the cache first, so any new Wasm
            // upload won't be cached. That's why we should look at the storage in its initial
            // state, which is conveniently provided by the recording mode snapshot.
            #[cfg(any(test, feature = "recording_mode"))]
            let init_value = if host.in_storage_recording_mode()? {
                storage.get_snapshot_value(host, k)?
            } else {
                v.clone()
            };
            #[cfg(any(test, feature = "recording_mode"))]
            let v = &init_value;

            if let LedgerKey::ContractCode(_) = &**k {
                if let Some((e, _)) = v {
                    if let LedgerEntryData::ContractCode(ContractCodeEntry { code, hash, ext }) =
                        &e.data
                    {
                        // We allow empty contracts in testing mode; they exist
                        // to exercise as much of the contract-code-storage
                        // infrastructure as possible, while still redirecting
                        // the actual execution into a `ContractFunctionSet`.
                        // They should never be called, so we do not have to go
                        // as far as making a fake `ParsedModule` for them.
                        if cfg!(any(test, feature = "testutils")) && code.as_slice().is_empty() {
                            continue;
                        }

                        let code_cost_inputs = match ext {
                            ContractCodeEntryExt::V0 => VersionedContractCodeCostInputs::V0 {
                                wasm_bytes: code.len(),
                            },
                            ContractCodeEntryExt::V1(v1) => VersionedContractCodeCostInputs::V1(
                                v1.cost_inputs.metered_clone(host.as_budget())?,
                            ),
                        };
                        self.parse_and_cache_module(host, hash, code, code_cost_inputs)?;
                    }
                }
            }
        }
        if !self.modules.is_reusable() {
            // Update the linkers to (only) include symbols mentioned in the added
            // modules. The initial (trivial, empty) linkers the ModuleCache is
            // constructed with have _no_ symbols, and limiting additions those
            // mentioned by any modules we're actually going to use will speed up
            // the next two lines constructing nontrivial linkers.
            self.linker = self.make_linker(host)?;
            self.wasmtime_linker = self.make_wasmtime_linker(host)?;
        }
        Ok(())
    }

    pub fn parse_and_cache_module_simple(
        &mut self,
        host: &Host,
        wasm: &[u8],
    ) -> Result<(), HostError> {
        let contract_id = Hash(crate::crypto::sha256_hash_from_bytes_raw(
            wasm,
            host.as_budget(),
        )?);
        self.parse_and_cache_module(
            host,
            &contract_id,
            wasm,
            VersionedContractCodeCostInputs::V0 {
                wasm_bytes: wasm.len(),
            },
        )
    }

    pub fn parse_and_cache_module(
        &mut self,
        host: &Host,
        contract_id: &Hash,
        wasm: &[u8],
        cost_inputs: VersionedContractCodeCostInputs,
    ) -> Result<(), HostError> {
        if self.modules.contains_key(contract_id, host.as_budget())? {
            if self.modules.is_reusable() {
                return Ok(());
            } else {
                return Err(host.err(
                    ScErrorType::Context,
                    ScErrorCode::InternalError,
                    "module cache already contains contract",
                    &[],
                ));
            }
        }
        let parsed_module =
            ParsedModule::new(host, &self.engine, &self.wasmtime_engine, &wasm, cost_inputs)?;
        self.modules.insert(
            contract_id.metered_clone(host)?,
            parsed_module,
            host.as_budget(),
        )?;
        Ok(())
    }

    pub fn with_import_symbols<T>(
        &self,
        host: &Host,
        callback: impl FnOnce(&BTreeSet<(&str, &str)>) -> Result<T, HostError>,
    ) -> Result<T, HostError> {
        let mut import_symbols = BTreeSet::new();
        let ModuleCacheMap::MeteredSingleUseMap(modules) = &self.modules else {
            return Err(host.err(
                ScErrorType::Context,
                ScErrorCode::InternalError,
                "with_import_symbols called on non-MeteredSingleUseMap cache",
                &[],
            ));
        };
        for module in modules.values(host.as_budget())? {
            module.with_import_symbols(host, |module_symbols| {
                for hf in HOST_FUNCTIONS {
                    let sym = (hf.mod_str, hf.fn_str);
                    if module_symbols.contains(&sym) {
                        import_symbols.insert(sym);
                    }
                }
                Ok(())
            })?;
        }
        // We approximate the cost of `BTreeSet` with the cost of initializng a
        // `Vec` with the same elements, and we are doing it after the set has
        // been created. The element count has been limited/charged during the
        // parsing phase, so there is no DOS factor. We don't charge for
        // insertion/lookups, since they should be cheap and number of
        // operations on the set is limited (only used during `Linker`
        // creation).
        Vec::<(&str, &str)>::charge_bulk_init_cpy(import_symbols.len() as u64, host)?;
        callback(&import_symbols)
    }

    pub fn make_linker(&self, host: &Host) -> Result<wasmi::Linker<Host>, HostError> {
        self.with_import_symbols(host, |symbols| Host::make_linker(&self.engine, symbols))
    }

    pub fn make_wasmtime_linker(&self, host: &Host) -> Result<wasmtime::Linker<Host>, HostError> {
        self.with_import_symbols(host, |symbols| {
            Host::make_wasmtime_linker(host, &self.wasmtime_engine, symbols)
        })
    }

    pub fn contains_module(&self, wasm_hash: &Hash, host: &Host) -> Result<bool, HostError> {
        Ok(self.modules.contains_key(wasm_hash, host.as_budget())?)
    }

    pub fn get_module(
        &self,
        host: &Host,
        wasm_hash: &Hash,
    ) -> Result<Option<Rc<ParsedModule>>, HostError> {
        if let Some(m) = self.modules.get(wasm_hash, host.as_budget())? {
            Ok(Some(m.clone()))
        } else {
            Ok(None)
        }
    }
}
