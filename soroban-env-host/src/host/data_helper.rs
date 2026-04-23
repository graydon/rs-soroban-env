use core::cmp::min;

use crate::{
    budget::AsBudget,
    err,
    host::metered_clone::MeteredClone,
    storage::{self, InstanceStorageMap, Storage},
    vm::VersionedContractCodeCostInputs,
    xdr::{
        AccountEntry, AccountId, Asset, BytesM, ContractCodeEntry, ContractDataDurability,
        ContractDataEntry, ContractExecutable, ContractId, ContractIdPreimage, ExtensionPoint,
        Hash, HashIdPreimage, HashIdPreimageContractId,
        LazyLedgerEntry, LazyLedgerKey, LedgerEntry,
        LedgerEntryData, LedgerEntryExt, LedgerEntryType, LedgerKey, LedgerKeyAccount,
        LedgerKeyContractCode, LedgerKeyContractData, LedgerKeyTrustLine, PublicKey,
        ScAddress, ScContractInstance, ScErrorCode, ScErrorType, ScMap, ScVal, ScValType,
        Signer, SignerKey, ThresholdIndexes, TrustLineAsset, Uint256,
        ContractCodeCostInputs, LazyScContractInstance,
    },
    AddressObject, Env, ErrorHandler, Host, HostError, StorageType, U32Val, Val,
};

impl Host {
    pub(crate) fn with_mut_storage<F, U>(&self, f: F) -> Result<U, HostError>
    where
        F: FnOnce(&mut Storage) -> Result<U, HostError>,
    {
        f(&mut *self.try_borrow_storage_mut()?)
    }

    /// Immutable accessor to the instance storage of the currently running
    /// contract.
    /// Performs lazy initialization of instance storage on access.
    pub(crate) fn with_instance_storage<F, U>(&self, f: F) -> Result<U, HostError>
    where
        F: FnOnce(&InstanceStorageMap) -> Result<U, HostError>,
    {
        self.with_current_context_mut(|ctx| {
            self.maybe_init_instance_storage(ctx)?;
            f(ctx.storage.as_ref().ok_or_else(|| {
                self.err(
                    ScErrorType::Context,
                    ScErrorCode::InternalError,
                    "missing instance storage",
                    &[],
                )
            })?)
        })
    }

    /// Mutable accessor to the instance storage of the currently running
    /// contract.
    /// Performs lazy initialization of instance storage on access.
    pub(crate) fn with_mut_instance_storage<F, U>(&self, f: F) -> Result<U, HostError>
    where
        F: FnOnce(&mut InstanceStorageMap) -> Result<U, HostError>,
    {
        self.with_current_context_mut(|ctx| {
            self.maybe_init_instance_storage(ctx)?;
            let storage = ctx.storage.as_mut().ok_or_else(|| {
                self.err(
                    ScErrorType::Context,
                    ScErrorCode::InternalError,
                    "missing instance storage",
                    &[],
                )
            })?;
            // Consider any mutable access to be modifying the instance storage.
            // This way we would provide consistent footprint (RO for read-only
            // ops using `with_instance_storage` and RW for potentially
            // mutating ops using `with_mut_instance_storage`).
            storage.is_modified = true;
            f(storage)
        })
    }

    pub(crate) fn contract_instance_ledger_key(
        &self,
        contract_id: &ContractId,
    ) -> Result<LazyLedgerKey, HostError> {
        let contract_id = contract_id.metered_clone(self)?;
        let eager = LedgerKey::ContractData(LedgerKeyContractData {
            key: ScVal::LedgerKeyContractInstance,
            durability: ContractDataDurability::Persistent,
            contract: ScAddress::Contract(contract_id),
        });
        storage::to_lazy_key(&eager)
    }

    pub(crate) fn extract_contract_instance_from_ledger_entry(
        &self,
        entry: &LedgerEntry,
    ) -> Result<ScContractInstance, HostError> {
        match &entry.data {
            LedgerEntryData::ContractData(e) => match &e.val {
                ScVal::ContractInstance(instance) => instance.metered_clone(self),
                _ => Err(self.err(
                    ScErrorType::Storage,
                    ScErrorCode::InternalError,
                    "ledger entry for contract instance does not contain contract instance",
                    &[],
                )),
            },
            _ => Err(self.err(
                ScErrorType::Storage,
                ScErrorCode::InternalError,
                "expected ContractData ledger entry",
                &[],
            )),
        }
    }

    // Notes on metering: retrieving from storage covered. Rest are free.
    pub(crate) fn retrieve_contract_instance_from_storage(
        &self,
        key: &LazyLedgerKey,
    ) -> Result<LazyScContractInstance, HostError> {
        let lazy_entry = self.try_borrow_storage_mut()?.get(key, self, None)?;
        // Use lazy accessors: entry.data → contract_data → val → contract_instance
        let data = lazy_entry.data();
        let contract_data = data.as_contract_data().ok_or_else(|| {
            self.err(
                ScErrorType::Storage,
                ScErrorCode::InternalError,
                "expected ContractData ledger entry",
                &[],
            )
        })?;
        let val = contract_data.val();
        if val.discriminant() != ScValType::ContractInstance {
            return Err(self.err(
                ScErrorType::Storage,
                ScErrorCode::InternalError,
                "ledger entry for contract instance does not contain contract instance",
                &[],
            ));
        }
        val.as_contract_instance().ok_or_else(|| {
            self.err(
                ScErrorType::Storage,
                ScErrorCode::InternalError,
                "failed to extract lazy contract instance",
                &[],
            )
        })
    }

    pub(crate) fn contract_code_ledger_key(
        &self,
        wasm_hash: &Hash,
    ) -> Result<LazyLedgerKey, HostError> {
        let wasm_hash = wasm_hash.metered_clone(self)?;
        let eager = LedgerKey::ContractCode(LedgerKeyContractCode { hash: wasm_hash });
        storage::to_lazy_key(&eager)
    }

    pub(crate) fn retrieve_wasm_from_storage(
        &self,
        wasm_hash: &Hash,
    ) -> Result<(BytesM, VersionedContractCodeCostInputs), HostError> {
        let key = self.contract_code_ledger_key(wasm_hash)?;
        let lazy_entry = self.try_borrow_storage_mut()?.get(&key, self, None)?;
        // Use lazy accessors: entry.data → contract_code → code/ext
        let data = lazy_entry.data();
        let lazy_code = data.as_contract_code().ok_or_else(|| {
            err!(
                self,
                (ScErrorType::Storage, ScErrorCode::InternalError),
                "expected ContractCode ledger entry",
                *wasm_hash
            )
        })?;
        // Extract the WASM code bytes from the lazy handle — this copies the bytes
        let code_bytes = lazy_code.code();
        let code = BytesM::try_from(code_bytes.as_bytes()).map_err(|_| {
            err!(
                self,
                (ScErrorType::Storage, ScErrorCode::InternalError),
                "invalid wasm code bytes",
                *wasm_hash
            )
        })?;
        // Extract cost inputs from the extension
        let lazy_ext = lazy_code.ext();
        let costs = match lazy_ext.discriminant_i32() {
            0 => {
                // V0: no cost inputs, just wasm bytes length
                VersionedContractCodeCostInputs::V0 {
                    wasm_bytes: code.len(),
                }
            }
            1 => {
                // V1: has cost inputs — deserialize just the ext sub-region
                let eager_ext =
                    crate::xdr::ContractCodeEntryExt::try_from(&lazy_ext)
                    .map_err(|_| {
                        err!(
                            self,
                            (ScErrorType::Storage, ScErrorCode::InternalError),
                            "failed to parse contract code ext",
                            *wasm_hash
                        )
                    })?;
                match eager_ext {
                    crate::xdr::ContractCodeEntryExt::V1(v1) => {
                        VersionedContractCodeCostInputs::V1(
                            v1.cost_inputs.metered_clone(self.as_budget())?,
                        )
                    }
                    _ => {
                        return Err(err!(
                            self,
                            (ScErrorType::Storage, ScErrorCode::InternalError),
                            "expected V1 ext",
                            *wasm_hash
                        ));
                    }
                }
            }
            _ => {
                return Err(err!(
                    self,
                    (ScErrorType::Storage, ScErrorCode::InternalError),
                    "unknown contract code ext version",
                    *wasm_hash
                ));
            }
        };
        Ok((code, costs))
    }

    pub(crate) fn wasm_exists(&self, wasm_hash: &Hash) -> Result<bool, HostError> {
        let key = self.contract_code_ledger_key(wasm_hash)?;
        self.try_borrow_storage_mut()?.has(&key, self, None)
    }

    // Stores the contract instance specified with its parts (executable and
    // storage).
    // When either of parts is `None`, the old value is preserved (when
    // existent).
    // `executable` has to be present for newly created contract instances.
    // Notes on metering: `from_host_obj` and `put` to storage covered, rest are free.
    pub(crate) fn store_contract_instance(
        &self,
        executable: Option<ContractExecutable>,
        instance_storage: Option<ScMap>,
        contract_id: ContractId,
        key: &LazyLedgerKey,
    ) -> Result<(), HostError> {
        if self.try_borrow_storage_mut()?.has(key, self, None)? {
            let (lazy_current, live_until_ledger) = self
                .try_borrow_storage_mut()?
                .get_with_live_until_ledger(key, self, None)?;
            // COW: must deserialize to modify, then re-serialize
            let mut current = storage::from_lazy_entry(&lazy_current)?;

            if let LedgerEntryData::ContractData(ref mut entry) = current.data {
                if let ScVal::ContractInstance(ref mut instance) = entry.val {
                    if let Some(executable) = executable {
                        instance.executable = executable;
                    }
                    if let Some(storage) = instance_storage {
                        instance.storage = Some(storage);
                    }
                } else {
                    return Err(self.err(
                        ScErrorType::Storage,
                        ScErrorCode::InternalError,
                        "expected ScVal::ContractInstance for contract instance",
                        &[],
                    ));
                }
            } else {
                return Err(self.err(
                    ScErrorType::Storage,
                    ScErrorCode::InternalError,
                    "expected DataEntry for contract instance",
                    &[],
                ));
            }

            self.try_borrow_storage_mut()?.put(
                key,
                &storage::to_lazy_entry(&current)?,
                live_until_ledger,
                self,
                None,
            )?;
        } else {
            let data = ContractDataEntry {
                contract: ScAddress::Contract(contract_id.metered_clone(self)?),
                key: ScVal::LedgerKeyContractInstance,
                val: ScVal::ContractInstance(ScContractInstance {
                    executable: executable.ok_or_else(|| {
                        self.err(
                            ScErrorType::Context,
                            ScErrorCode::InternalError,
                            "can't initialize contract without executable",
                            &[],
                        )
                    })?,
                    storage: instance_storage,
                }),
                durability: ContractDataDurability::Persistent,
                ext: ExtensionPoint::V0,
            };
            self.try_borrow_storage_mut()?.put(
                key,
                &Host::new_contract_data(self, data)?,
                Some(self.get_min_live_until_ledger(ContractDataDurability::Persistent)?),
                self,
                None,
            )?;
        }
        Ok(())
    }

    pub(crate) fn extend_contract_code_ttl_from_contract_id(
        &self,
        instance_key: LazyLedgerKey,
        threshold: u32,
        extend_to: u32,
    ) -> Result<(), HostError> {
        let lazy_exec = self
            .retrieve_contract_instance_from_storage(&instance_key)?
            .executable();
        if let Some(lazy_hash) = lazy_exec.as_wasm() {
            let wasm_hash = Hash::try_from(&lazy_hash).map_err(|_| {
                HostError::from((ScErrorType::Storage, ScErrorCode::InternalError))
            })?;
            let key = self.contract_code_ledger_key(&wasm_hash)?;
            self.try_borrow_storage_mut()?
                .extend_ttl(self, key, threshold, extend_to, None)?;
        }
        Ok(())
    }

    pub(crate) fn extend_contract_instance_ttl_from_contract_id(
        &self,
        instance_key: LazyLedgerKey,
        threshold: u32,
        extend_to: u32,
    ) -> Result<(), HostError> {
        self.try_borrow_storage_mut()?.extend_ttl(
            self,
            instance_key.clone(),
            threshold,
            extend_to,
            None,
        )?;
        Ok(())
    }

    pub(crate) fn extend_contract_code_ttl_v2(
        &self,
        instance_key: &LazyLedgerKey,
        extend_to: u32,
        min_extension: u32,
        max_extension: u32,
    ) -> Result<(), HostError> {
        let lazy_exec = self
            .retrieve_contract_instance_from_storage(instance_key)?
            .executable();
        if let Some(lazy_hash) = lazy_exec.as_wasm() {
            let wasm_hash = Hash::try_from(&lazy_hash).map_err(|_| {
                HostError::from((ScErrorType::Storage, ScErrorCode::InternalError))
            })?;
            let key = self.contract_code_ledger_key(&wasm_hash)?;
            self.try_borrow_storage_mut()?.extend_ttl_v2(
                self,
                key,
                extend_to,
                min_extension,
                max_extension,
                None,
            )?;
        }
        Ok(())
    }

    pub(crate) fn extend_contract_instance_ttl_v2(
        &self,
        instance_key: LazyLedgerKey,
        extend_to: u32,
        min_extension: u32,
        max_extension: u32,
    ) -> Result<(), HostError> {
        self.try_borrow_storage_mut()?.extend_ttl_v2(
            self,
            instance_key,
            extend_to,
            min_extension,
            max_extension,
            None,
        )?;
        Ok(())
    }

    // metering: covered by components
    pub(crate) fn get_full_contract_id_preimage(
        &self,
        init_preimage: ContractIdPreimage,
    ) -> Result<HashIdPreimage, HostError> {
        Ok(HashIdPreimage::ContractId(HashIdPreimageContractId {
            network_id: self
                .hash_from_bytesobj_input("network_id", self.get_ledger_network_id()?)?,
            contract_id_preimage: init_preimage,
        }))
    }

    // notes on metering: `get` from storage is covered. Rest are free.
    pub(crate) fn load_account(&self, account_id: AccountId) -> Result<AccountEntry, HostError> {
        let acc = self.to_account_key(account_id)?;
        self.with_mut_storage(|storage| {
            let lazy_entry = storage.get(&acc, self, None)?;
            // Use lazy accessor to check discriminant, then deserialize just
            // the AccountEntry sub-region (not the full LedgerEntry envelope).
            let data = lazy_entry.data();
            if data.discriminant() != LedgerEntryType::Account {
                return Err(err!(
                    self,
                    (ScErrorType::Storage, ScErrorCode::InternalError),
                    "ledger entry is not account",
                    data.discriminant().name()
                ));
            }
            let lazy_account = data.as_account().ok_or_else(|| {
                err!(
                    self,
                    (ScErrorType::Storage, ScErrorCode::InternalError),
                    "failed to extract lazy account",
                    ""
                )
            })?;
            // Deserialize just the AccountEntry sub-region
            AccountEntry::try_from(&lazy_account).map_err(|_| {
                HostError::from((ScErrorType::Storage, ScErrorCode::InternalError))
            })
        })
    }

    pub(crate) fn to_account_key(&self, account_id: AccountId) -> Result<LazyLedgerKey, HostError> {
        let eager = LedgerKey::Account(LedgerKeyAccount { account_id });
        storage::to_lazy_key(&eager)
    }

    pub(crate) fn create_asset_4(&self, asset_code: [u8; 4], issuer: AccountId) -> Asset {
        use crate::xdr::{AlphaNum4, AssetCode4};
        Asset::CreditAlphanum4(AlphaNum4 {
            asset_code: AssetCode4(asset_code),
            issuer,
        })
    }

    pub(crate) fn create_asset_12(&self, asset_code: [u8; 12], issuer: AccountId) -> Asset {
        use crate::xdr::{AlphaNum12, AssetCode12};
        Asset::CreditAlphanum12(AlphaNum12 {
            asset_code: AssetCode12(asset_code),
            issuer,
        })
    }

    pub(crate) fn to_trustline_key(
        &self,
        account_id: AccountId,
        asset: TrustLineAsset,
    ) -> Result<LazyLedgerKey, HostError> {
        let eager = LedgerKey::Trustline(LedgerKeyTrustLine { account_id, asset });
        storage::to_lazy_key(&eager)
    }

    pub(crate) fn get_signer_weight_from_account(
        &self,
        target_signer: Uint256,
        account: &AccountEntry,
    ) -> Result<u8, HostError> {
        if account.account_id
            == AccountId(PublicKey::PublicKeyTypeEd25519(
                target_signer.metered_clone(self)?,
            ))
        {
            // Target signer is the master key, so return the master weight
            let Some(threshold) = account
                .thresholds
                .0
                .get(ThresholdIndexes::MasterWeight as usize)
            else {
                return Err(self.error(
                    (ScErrorType::Value, ScErrorCode::InternalError).into(),
                    "unexpected thresholds-array size",
                    &[],
                ));
            };
            Ok(*threshold)
        } else {
            // Target signer is not the master key, so search the account signers
            let signers: &Vec<Signer> = account.signers.as_ref();
            for signer in signers {
                if let SignerKey::Ed25519(ref this_signer) = signer.key {
                    if &target_signer == this_signer {
                        // Clamp the weight at 255. Stellar protocol before v10
                        // allowed weights to exceed 255, but the max threshold
                        // is 255, hence there is no point in having a larger
                        // weight.
                        let weight = min(signer.weight, u8::MAX as u32);
                        // We've found the target signer in the account signers, so return the weight
                        return weight.try_into().map_err(|_| {
                            self.err(
                                ScErrorType::Auth,
                                ScErrorCode::ArithDomain,
                                "signer weight does not fit in u8",
                                &[U32Val::from(weight).to_val()],
                            )
                        });
                    }
                }
            }
            // We didn't find the target signer, return 0 weight to indicate that.
            Ok(0u8)
        }
    }

    pub(crate) fn new_contract_data(
        &self,
        data: ContractDataEntry,
    ) -> Result<LazyLedgerEntry, HostError> {
        let eager = LedgerEntry {
            // This is modified to the appropriate value on the core side during
            // commiting the ledger transaction.
            last_modified_ledger_seq: 0,
            data: LedgerEntryData::ContractData(data),
            ext: LedgerEntryExt::V0,
        };
        storage::to_lazy_entry(&eager)
    }

    pub(crate) fn new_contract_code(
        &self,
        data: ContractCodeEntry,
    ) -> Result<LazyLedgerEntry, HostError> {
        let eager = LedgerEntry {
            // This is modified to the appropriate value on the core side during
            // commiting the ledger transaction.
            last_modified_ledger_seq: 0,
            data: LedgerEntryData::ContractCode(data),
            ext: LedgerEntryExt::V0,
        };
        storage::to_lazy_entry(&eager)
    }

    pub(crate) fn modify_ledger_entry_data(
        &self,
        original_entry: &LedgerEntry,
        new_data: LedgerEntryData,
    ) -> Result<LazyLedgerEntry, HostError> {
        let eager = LedgerEntry {
            // This is modified to the appropriate value on the core side during
            // commiting the ledger transaction.
            last_modified_ledger_seq: 0,
            data: new_data,
            ext: original_entry.ext.metered_clone(self)?,
        };
        storage::to_lazy_entry(&eager)
    }

    pub(crate) fn contract_id_from_scaddress(
        &self,
        address: ScAddress,
    ) -> Result<ContractId, HostError> {
        match address {
            ScAddress::Contract(contract_id) => Ok(contract_id),
            _ => Err(self.err(
                ScErrorType::Object,
                ScErrorCode::InvalidInput,
                "not a contract address",
                &[],
            )),
        }
    }

    pub(crate) fn contract_id_from_address(
        &self,
        address: AddressObject,
    ) -> Result<ContractId, HostError> {
        let lazy = self.get_lazy_obj(address)?;
        let la = lazy.as_address().ok_or_else(|| HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType)))?;
        let addr = ScAddress::try_from(&la)?;
        self.contract_id_from_scaddress(addr)
    }

    pub(super) fn put_contract_data_into_ledger(
        &self,
        k: Val,
        v: Val,
        t: StorageType,
    ) -> Result<(), HostError> {
        let durability: ContractDataDurability = t.try_into()?;
        let lazy_key = self.storage_key_from_val(k, durability)?;
        // Currently the storage stores the whole ledger entries, while this
        // operation might only modify the internal `ScVal` value. Thus we
        // need to only overwrite the value in case if there is already an
        // existing ledger entry value for the key in the storage.
        if self.try_borrow_storage_mut()?.has(&lazy_key, self, Some(k))? {
            let (lazy_current, live_until_ledger) = self
                .try_borrow_storage_mut()?
                .get_with_live_until_ledger(&lazy_key, self, Some(k))?;
            // COW: must deserialize to modify, then re-serialize
            let mut current = storage::from_lazy_entry(&lazy_current)?;
            match current.data {
                LedgerEntryData::ContractData(ref mut entry) => {
                    entry.val = self.from_host_val(v)?;
                }
                _ => {
                    return Err(self.err(
                        ScErrorType::Storage,
                        ScErrorCode::InternalError,
                        "expected DataEntry",
                        &[],
                    ));
                }
            }
            self.try_borrow_storage_mut()?.put(
                &lazy_key,
                &storage::to_lazy_entry(&current)?,
                live_until_ledger,
                self,
                Some(k),
            )?;
        } else {
            let data = ContractDataEntry {
                contract: ScAddress::Contract(self.get_current_contract_id_internal()?),
                key: self.from_host_val(k)?,
                val: self.from_host_val(v)?,
                durability,
                ext: ExtensionPoint::V0,
            };
            self.try_borrow_storage_mut()?.put(
                &lazy_key,
                &Host::new_contract_data(self, data)?,
                Some(self.get_min_live_until_ledger(durability)?),
                self,
                Some(k),
            )?;
        }

        Ok(())
    }
}

#[cfg(any(test, feature = "testutils"))]
use crate::crypto;
#[cfg(any(test, feature = "testutils"))]
use crate::storage::{AccessType, EntryWithLiveUntil, Footprint};

#[cfg(any(test, feature = "testutils"))]
impl Host {
    /// Writes an arbitrary ledger entry to storage.
    pub fn add_ledger_entry(
        &self,
        key: &LazyLedgerKey,
        val: &LazyLedgerEntry,
        live_until_ledger: Option<u32>,
    ) -> Result<(), HostError> {
        self.with_mut_storage(|storage| storage.put(key, val, live_until_ledger, self, None))
    }

    /// Reads an arbitrary ledger entry from the storage.
    ///
    /// Returns `None` if the entry does not exist.
    pub fn get_ledger_entry(
        &self,
        key: &LazyLedgerKey,
    ) -> Result<Option<EntryWithLiveUntil>, HostError> {
        self.with_mut_storage(|storage| storage.try_get_full(key, self, None))
    }

    /// Returns all the ledger entries stored in the storage as key-value pairs.
    #[allow(clippy::type_complexity)]
    pub fn get_stored_entries(
        &self,
    ) -> Result<Vec<(LazyLedgerKey, Option<EntryWithLiveUntil>)>, HostError> {
        self.with_mut_storage(|storage| Ok(storage.map.map.clone()))
    }

    // Performs the necessary setup to access the provided ledger key/entry in
    // enforcing storage mode.
    pub fn setup_storage_entry(
        &self,
        key: LazyLedgerKey,
        val: Option<(LazyLedgerEntry, Option<u32>)>,
        access_type: AccessType,
    ) -> Result<(), HostError> {
        self.with_mut_storage(|storage| {
            storage
                .footprint
                .record_access(&key, access_type, self.as_budget())?;
            storage.map = storage.map.insert(key, val, self.as_budget())?;
            Ok(())
        })
    }

    // Performs the necessary setup to access all the entries in provided
    // footprint in enforcing mode.
    // "testutils" are not covered by budget metering.
    pub fn setup_storage_footprint(&self, footprint: Footprint) -> Result<(), HostError> {
        for (key, access_type) in footprint.0.map {
            self.setup_storage_entry(key, None, access_type)?;
        }
        Ok(())
    }

    // Checks whether the given contract has a special 'dummy' executable
    // that marks contracts created with `register_test_contract`.
    pub(crate) fn is_test_contract_executable(
        &self,
        contract_id: &ContractId,
    ) -> Result<bool, HostError> {
        let key = self.contract_instance_ledger_key(contract_id)?;
        let lazy_instance = self.retrieve_contract_instance_from_storage(&key)?;
        let lazy_exec = lazy_instance.executable();
        if let Some(lazy_hash) = lazy_exec.as_wasm() {
            let wasm_hash = Hash::try_from(&lazy_hash).map_err(|_| {
                HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
            })?;
            let test_hash: Hash = crypto::sha256_hash_from_bytes(&[], self)?
                .try_into()
                .map_err(|_| {
                    self.err(
                        ScErrorType::Value,
                        ScErrorCode::InternalError,
                        "unexpected hash length",
                        &[],
                    )
                })?;
            Ok(wasm_hash == test_hash)
        } else {
            Ok(false)
        }
    }

    #[cfg(test)]
    pub(crate) fn create_tl_asset_4(
        &self,
        asset_code: [u8; 4],
        issuer: AccountId,
    ) -> TrustLineAsset {
        use crate::xdr::{AlphaNum4, AssetCode4};
        TrustLineAsset::CreditAlphanum4(AlphaNum4 {
            asset_code: AssetCode4(asset_code),
            issuer,
        })
    }

    #[cfg(test)]
    pub(crate) fn create_tl_asset_12(
        &self,
        asset_code: [u8; 12],
        issuer: AccountId,
    ) -> TrustLineAsset {
        use crate::xdr::{AlphaNum12, AssetCode12};
        TrustLineAsset::CreditAlphanum12(AlphaNum12 {
            asset_code: AssetCode12(asset_code),
            issuer,
        })
    }
}
