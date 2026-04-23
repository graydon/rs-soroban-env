use crate::host_object::MuxedScAddress;
use crate::{
    budget::{AsBudget, DepthLimiter},
    crypto::metered_scalar::MeteredScalar,
    err,
    host::metered_clone::{
        charge_shallow_copy, MeteredAlloc, MeteredClone, MeteredContainer, MeteredIterator,
    },
    host::metered_map::MeteredOrdMap,
    num::{i256_from_pieces, i256_into_pieces, u256_from_pieces, u256_into_pieces},
    storage,
    xdr::{
        self, int128_helpers, AccountId, ContractCostType, ContractDataDurability, ContractId,
        Hash, Int128Parts, Int256Parts, LazyLedgerKey, LedgerKey, LedgerKeyContractData,
        MuxedEd25519Account, PublicKey, ScAddress, ScBytes, ScErrorCode, ScErrorType, ScMap,
        ScMapEntry, ScSymbol, ScVal, ScVec, UInt128Parts, UInt256Parts, Uint256, VecM,
    },
    AddressObject, BytesObject, Convert, Host, HostError, Object, ScValObjRef, ScValObject, Symbol,
    SymbolObject, TryFromVal, TryIntoVal, U256Val, U32Val, Val, VecObject,
};

use super::ErrorHandler;

impl Host {
    // Notes on metering: free
    pub(crate) fn usize_to_u32(&self, u: usize) -> Result<u32, HostError> {
        match u32::try_from(u) {
            Ok(v) => Ok(v),
            Err(_) => Err(self.err(
                ScErrorType::Value,
                ScErrorCode::ArithDomain,
                "provided usize does not fit in u32",
                &[],
            )),
        }
    }

    // Notes on metering: free
    pub(crate) fn usize_to_u32val(&self, u: usize) -> Result<U32Val, HostError> {
        self.usize_to_u32(u).map(|v| v.into())
    }

    pub(crate) fn u256_from_account(&self, account_id: &AccountId) -> Result<Uint256, HostError> {
        let crate::xdr::PublicKey::PublicKeyTypeEd25519(ed25519) =
            account_id.metered_clone(self)?.0;
        Ok(ed25519)
    }

    // Notes on metering: free
    pub(crate) fn u8_from_u32val_input(
        &self,
        name: &'static str,
        r: U32Val,
    ) -> Result<u8, HostError> {
        let u: u32 = r.into();
        match u8::try_from(u) {
            Ok(v) => Ok(v),
            Err(_) => Err(self.err(
                ScErrorType::Value,
                ScErrorCode::ArithDomain,
                "expecting U32Val less than 256",
                &[r.to_val(), name.try_into_val(self)?],
            )),
        }
    }

    pub(crate) fn hash_from_bytesobj_input(
        &self,
        name: &'static str,
        hash: BytesObject,
    ) -> Result<Hash, HostError> {
        static_assertions::assert_eq_size!([u8; 32], Hash);
        self.fixed_length_bytes_from_bytesobj_input::<Hash, 32>(name, hash)
    }

    pub(crate) fn u256_from_bytesobj_input(
        &self,
        name: &'static str,
        u256: BytesObject,
    ) -> Result<Uint256, HostError> {
        static_assertions::assert_eq_size!([u8; 32], Uint256);
        self.fixed_length_bytes_from_bytesobj_input::<Uint256, 32>(name, u256)
    }

    pub(crate) fn fixed_length_bytes_from_slice<T, const N: usize>(
        &self,
        name: &'static str,
        bytes_arr: &[u8],
    ) -> Result<T, HostError>
    where
        T: From<[u8; N]>,
    {
        match <[u8; N]>::try_from(bytes_arr) {
            Ok(arr) => {
                self.charge_budget(ContractCostType::MemCpy, Some(N as u64))?;
                Ok(arr.into())
            }
            Err(_) => Err(err!(
                self,
                (ScErrorType::Object, ScErrorCode::UnexpectedSize),
                "expected fixed-length bytes slice, got slice with different size",
                name,
                N,
                bytes_arr.len()
            )),
        }
    }

    pub(crate) fn fixed_length_bytes_from_bytesobj_input<T, const N: usize>(
        &self,
        name: &'static str,
        obj: BytesObject,
    ) -> Result<T, HostError>
    where
        T: From<[u8; N]>,
    {
        let lazy = self.get_lazy_obj(Object::try_from(obj.to_val()).unwrap())?;
        let bytes = lazy.as_bytes().ok_or_else(|| {
            HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType))
        })?;
        self.fixed_length_bytes_from_slice(name, bytes.as_bytes())
    }

    pub(crate) fn account_id_from_bytesobj(&self, k: BytesObject) -> Result<AccountId, HostError> {
        let lazy = self.get_lazy_obj(Object::try_from(k.to_val()).unwrap())?;
        let bytes = lazy.as_bytes().ok_or_else(|| {
            HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType))
        })?;
        Ok(AccountId(xdr::PublicKey::PublicKeyTypeEd25519(
            self.fixed_length_bytes_from_slice("account_id", bytes.as_bytes())?,
        )))
    }

    pub(crate) fn storage_key_for_address(
        &self,
        contract: ScAddress,
        key: ScVal,
        durability: ContractDataDurability,
    ) -> Result<LazyLedgerKey, HostError> {
        let eager = LedgerKey::ContractData(LedgerKeyContractData {
            contract,
            key,
            durability,
        });
        storage::to_lazy_key(&eager)
    }

    pub(crate) fn storage_key_from_scval(
        &self,
        key: ScVal,
        durability: ContractDataDurability,
    ) -> Result<LazyLedgerKey, HostError> {
        let contract_id = self.get_current_contract_id_internal()?;
        self.storage_key_for_address(ScAddress::Contract(contract_id), key, durability)
    }

    /// Converts a [`Val`] to an [`ScVal`] and combines it with the currently-executing
    /// [`ContractID`] to produce a [`Key`], that can be used to access ledger [`Storage`].
    // Notes on metering: covered by components.
    pub(crate) fn storage_key_from_val(
        &self,
        k: Val,
        durability: ContractDataDurability,
    ) -> Result<LazyLedgerKey, HostError> {
        let key_scval = self.from_host_val_for_storage(k)?;
        self.storage_key_from_scval(key_scval, durability)
    }

    /// Converts a binary search result into a u64. `res` is `Some(index)` if
    /// the value was found at `index`, or `Err(index)` if the value was not
    /// found and would've needed to be inserted at `index`. Returns a
    /// Some(res_u64) where:
    /// - The high 32 bits is 0x0000_0001 if element existed or 0x0000_0000 if
    ///   it didn't
    /// - The low 32 bits contains the u32 representation of the `index` Err(_)
    ///   if the `index` fails to be converted to an u32.
    pub(crate) fn u64_from_binary_search_result(
        &self,
        res: Result<usize, usize>,
    ) -> Result<u64, HostError> {
        match res {
            Ok(u) => {
                let v = self.usize_to_u32(u)?;
                Ok(u64::from(v) | (1_u64 << u32::BITS))
            }
            Err(u) => {
                let v = self.usize_to_u32(u)?;
                Ok(u64::from(v))
            }
        }
    }

    pub(crate) fn call_args_from_obj(&self, args: VecObject) -> Result<Vec<Val>, HostError> {
        let lazy = self.get_lazy_obj(Object::try_from(args.to_val()).unwrap())?;
        let scval = ScVal::try_from(&lazy).map_err(|_| {
            HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
        })?;
        match scval {
            ScVal::Vec(Some(v)) => self.scvals_to_val_vec(v.as_slice()),
            _ => Err(HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType))),
        }
    }

    // Metering: covered by vals_to_vec
    pub(crate) fn vecobject_to_scval_vec(&self, args: VecObject) -> Result<VecM<ScVal>, HostError> {
        let lazy = self.get_lazy_obj(Object::try_from(args.to_val()).unwrap())?;
        let scval = ScVal::try_from(&lazy).map_err(|_| {
            HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
        })?;
        match scval {
            ScVal::Vec(Some(v)) => Ok(VecM::try_from(v.to_vec())?),
            _ => Err(HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType))),
        }
    }

    pub(crate) fn vals_to_scval_vec(&self, vals: &[Val]) -> Result<VecM<ScVal>, HostError> {
        vals.iter()
            .map(|v| self.from_host_val(*v))
            .metered_collect::<Result<Vec<ScVal>, HostError>>(self)??
            .try_into()
            .map_err(|_| {
                err!(
                    self,
                    (ScErrorType::Object, ScErrorCode::ExceededLimit),
                    "vector size limit exceeded",
                    vals.len()
                )
            })
    }

    pub(crate) fn scvals_to_val_vec(&self, scvals: &[ScVal]) -> Result<Vec<Val>, HostError> {
        scvals
            .iter()
            .map(|scv| self.to_host_val(scv))
            .metered_collect::<Result<Vec<Val>, HostError>>(self)?
    }

    pub(crate) fn bytesobj_from_internal_contract_id(
        &self,
    ) -> Result<Option<BytesObject>, HostError> {
        if let Some(id) = self.get_current_contract_id_opt_internal()? {
            let obj = self.add_obj_bytes(
                self.metered_slice_to_vec(id.0.as_slice())?.try_into()?,
            )?;
            Ok(Some(obj))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn scbytes_from_vec(&self, v: Vec<u8>) -> Result<ScBytes, HostError> {
        Ok(ScBytes(v.try_into()?))
    }

    pub(crate) fn metered_slice_to_vec(&self, s: &[u8]) -> Result<Vec<u8>, HostError> {
        Vec::<u8>::charge_bulk_init_cpy(s.len() as u64, self)?;
        Ok(s.to_vec())
    }

    // metering: covered
    pub(crate) fn scbytes_from_slice(&self, s: &[u8]) -> Result<ScBytes, HostError> {
        self.scbytes_from_vec(self.metered_slice_to_vec(s)?)
    }

    pub(crate) fn scbytes_from_hash(&self, hash: &Hash) -> Result<ScBytes, HostError> {
        self.scbytes_from_slice(hash.as_slice())
    }

    pub fn scaddress_from_address(&self, address: AddressObject) -> Result<ScAddress, HostError> {
        let lazy = self.get_lazy_obj(Object::try_from(address.to_val()).unwrap())?;
        let scval = ScVal::try_from(&lazy).map_err(|_| {
            HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
        })?;
        match scval {
            ScVal::Address(addr) => Ok(addr),
            _ => Err(HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType))),
        }
    }

    pub(crate) fn scsymbol_from_symbol(&self, symbol: Symbol) -> Result<ScSymbol, HostError> {
        if let Ok(sobj) = SymbolObject::try_from(symbol) {
            let lazy = self.get_lazy_obj(Object::try_from(sobj.to_val()).unwrap())?;
            let lazy_sym = lazy.as_symbol().ok_or_else(|| {
                HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType))
            })?;
            Ok(ScSymbol(lazy_sym.as_bytes().to_vec().try_into()?))
        } else {
            self.map_err(ScSymbol::try_from_val(self, &symbol))
        }
    }

    pub(crate) fn host_map_to_scmap(&self, map: &MeteredOrdMap<Val, Val, Host>) -> Result<ScMap, HostError> {
        let mut mv = Vec::<ScMapEntry>::with_metered_capacity(map.len(), self)?;
        for (k, v) in map.iter(self)? {
            let key = self.from_host_val(*k)?;
            let val = self.from_host_val(*v)?;
            mv.push(ScMapEntry { key, val });
        }
        Ok(ScMap(self.map_err(mv.try_into())?))
    }

    // This function is almost identical to `host_map_to_scmap`, and should only
    // be used for creating the instance storage map.
    pub(crate) fn instance_storage_map_to_scmap(&self, map: &MeteredOrdMap<Val, Val, Host>) -> Result<ScMap, HostError> {
        let mut mv = Vec::<ScMapEntry>::with_metered_capacity(map.len(), self)?;
        for (k, v) in map.iter(self)? {
            // This is the only difference point compared to `host_map_to_scmap`:
            // we convert the key according to the storage key conversion rules
            // instead of the general value conversion rules.
            let key = self.from_host_val_for_storage(*k)?;
            let val = self.from_host_val(*v)?;
            mv.push(ScMapEntry { key, val });
        }
        Ok(ScMap(self.map_err(mv.try_into())?))
    }

    /// Convert a VecObject of U256Val elements to a Vec of MeteredScalar
    pub(crate) fn metered_scalar_vec_from_vecobj<S>(
        &self,
        vp: VecObject,
    ) -> Result<Vec<S>, HostError>
    where
        S: MeteredScalar,
    {
        let lazy = self.get_lazy_obj(Object::try_from(vp.to_val()).unwrap())?;
        let scval = ScVal::try_from(&lazy).map_err(|_| {
            HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
        })?;
        let v = match scval {
            ScVal::Vec(Some(v)) => v,
            _ => return Err(HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType))),
        };
        let mut scalars: Vec<S> = Vec::with_metered_capacity(v.len(), self)?;
        for e in v.iter() {
            let val = self.to_host_val(e)?;
            let u256_val = U256Val::try_from(val).map_err(|_| {
                self.err(
                    ScErrorType::Crypto,
                    ScErrorCode::InvalidInput,
                    "element must be U256Val",
                    &[val],
                )
            })?;
            let scalar = S::from_u256val(self, u256_val)?;
            scalars.push(scalar);
        }
        Ok(scalars)
    }

    /// Convert a Vec of MeteredScalar to a VecObject of U256Val elements
    pub(crate) fn metered_scalar_vec_to_vecobj<S>(
        &self,
        scalars: Vec<S>,
    ) -> Result<VecObject, HostError>
    where
        S: MeteredScalar,
    {
        let vals = scalars
            .into_iter()
            .map(|s| s.into_u256val(self))
            .metered_collect::<Result<Vec<_>, HostError>>(self)??;

        let scvals: Vec<ScVal> = vals
            .into_iter()
            .map(|v| self.from_host_val(v.to_val()))
            .collect::<Result<Vec<_>, _>>()?;
        let scvec = ScVec(scvals.try_into()?);
        self.add_obj_vec_scval(scvec)
    }

    /// Convert a VecObject representing a Vec<Vec<U256Val>> elements to a Vec<Vec<MeteredScalar>>
    pub(crate) fn metered_scalar_vec_of_vec_from_vecobj<S>(
        &self,
        vp: VecObject,
    ) -> Result<Vec<Vec<S>>, HostError>
    where
        S: MeteredScalar,
    {
        let lazy = self.get_lazy_obj(Object::try_from(vp.to_val()).unwrap())?;
        let scval = ScVal::try_from(&lazy).map_err(|_| {
            HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
        })?;
        let v = match scval {
            ScVal::Vec(Some(v)) => v,
            _ => return Err(HostError::from((ScErrorType::Object, ScErrorCode::UnexpectedType))),
        };
        let n_rows = v.len();
        let mut result = Vec::with_metered_capacity(n_rows, self)?;
        for row_scval in v.iter() {
            let row_val = self.to_host_val(row_scval)?;
            let row_obj = VecObject::try_from(row_val).map_err(|_| {
                self.err(
                    ScErrorType::Crypto,
                    ScErrorCode::InvalidInput,
                    "poseidon_permutation: row must be a vector",
                    &[row_val],
                )
            })?;

            let row_vec = self.metered_scalar_vec_from_vecobj::<S>(row_obj)?;
            result.push(row_vec);
        }
        Ok(result)
    }
}

impl Convert<&Object, ScValObject> for Host {
    type Error = HostError;
    fn convert(&self, ob: &Object) -> Result<ScValObject, Self::Error> {
        self.from_host_obj(*ob)
    }
}

impl Convert<Object, ScValObject> for Host {
    type Error = HostError;
    fn convert(&self, ob: Object) -> Result<ScValObject, Self::Error> {
        self.from_host_obj(ob)
    }
}

impl<'a> Convert<&ScValObjRef<'a>, Object> for Host {
    type Error = HostError;
    fn convert(&self, ob: &ScValObjRef<'a>) -> Result<Object, Self::Error> {
        self.to_host_obj(ob)
    }
}

impl<'a> Convert<ScValObjRef<'a>, Object> for Host {
    type Error = HostError;
    fn convert(&self, ob: ScValObjRef<'a>) -> Result<Object, Self::Error> {
        self.to_host_obj(&ob)
    }
}

impl Host {
    pub(crate) fn check_val_representable_scval(&self, scval: &ScVal) -> Result<(), HostError> {
        if Val::can_represent_scval(&scval) {
            Ok(())
        } else {
            Err(self.err(
                ScErrorType::Value,
                ScErrorCode::InternalError,
                "unexpected non-Val-representable ScVal type",
                &[Val::from_u32(scval.discriminant() as u32).into()],
            ))
        }
    }

    pub(crate) fn from_host_val(&self, val: Val) -> Result<ScVal, HostError> {
        // This is the depth limit checkpoint for `Val`->`ScVal` conversion.
        // Metering of val conversion happens only if an object is encountered,
        // and is done inside `from_host_obj`.
        let _span = tracy_span!("Val to ScVal");
        let scval = self.budget_cloned().with_limited_depth(|_| {
            ScVal::try_from_val(self, &val)
                .map_err(|cerr| self.error(cerr, "failed to convert host value to ScVal", &[val]))
        })?;
        // This is a check of internal logical consistency: we came _from_ a Val
        // so the ScVal definitely should have been representable.
        self.check_val_representable_scval(&scval)?;
        Ok(scval)
    }

    pub(crate) fn from_host_val_for_storage(&self, val: Val) -> Result<ScVal, HostError> {
        let _span = tracy_span!("Val to ScVal");
        *self.try_borrow_storage_key_conversion_active_mut()? = true;
        let scval_res = self.budget_cloned().with_limited_depth(|_| {
            ScVal::try_from_val(self, &val)
                .map_err(|cerr| self.error(cerr, "failed to convert host value to ScVal", &[val]))
        });
        *self.try_borrow_storage_key_conversion_active_mut()? = false;
        let scval = scval_res?;
        self.check_val_representable_scval(&scval)?;
        Ok(scval)
    }

    pub(crate) fn to_host_val(&self, v: &ScVal) -> Result<Val, HostError> {
        let _span = tracy_span!("ScVal to Val");
        // This is the depth limit checkpoint for `ScVal`->`Val` conversion.
        // Metering of val conversion happens only if an object is encountered,
        // and is done inside `to_host_obj`.
        self.budget_cloned().with_limited_depth(|_| {
            v.try_into_val(self)
                .map_err(|cerr| self.error(cerr, "failed to convert ScVal to host value", &[]))
        })
    }

    // Version of `to_host_val` for the internal cases where the value has to
    // be valid by construction (e.g. read from ledger).
    pub(crate) fn to_valid_host_val(&self, v: &ScVal) -> Result<Val, HostError> {
        self.to_host_val(v).map_err(|e| {
            if e.error.is_type(ScErrorType::Budget) {
                e
            } else {
                self.err(
                    ScErrorType::Value,
                    ScErrorCode::InternalError,
                    "unexpected non-Val-representable ScVal in internal conversion",
                    &[],
                )
            }
        })
    }

    /// Converts a `LazyScVal` to a `Val` without eagerly deserializing.
    /// Primitive types that fit directly in a `Val` (bool, void, error,
    /// u32, i32, small symbols, etc.) are converted immediately.
    /// Object types (Vec, Map, Bytes, u64, i64, u128, etc.) are wrapped
    /// in `HostObject::Lazy` and only materialized when the contract
    /// actually accesses them via typed host functions.
    pub(crate) fn lazy_scval_to_host_val(
        &self,
        lazy: &xdr::LazyScVal,
    ) -> Result<Val, HostError> {
        use soroban_env_common::{
            DurationSmall, Error as ValError, I128Small, I256Small, I64Small, SymbolSmall,
            TimepointSmall, U128Small, U256Small, U64Small, Void,
        };
        use xdr::ScValType;
        match lazy.discriminant() {
            ScValType::Bool => {
                let b = lazy.as_bool().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                Ok(Val::from_bool(b).into())
            }
            ScValType::Void => Ok(Val::from_void().into()),
            ScValType::Error => {
                // Deserialize just the error (4 bytes)
                let lazy_err = lazy.as_error().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                let err = xdr::ScError::try_from(&lazy_err).map_err(|_| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                let val_err = ValError::try_from(err).map_err(|_| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                Ok(val_err.to_val())
            }
            ScValType::U32 => {
                let u = lazy.as_u32().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                Ok(Val::from_u32(u).into())
            }
            ScValType::I32 => {
                let i = lazy.as_i32().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                Ok(Val::from_i32(i).into())
            }
            ScValType::U64 => {
                let u = lazy.as_u64().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                if let Ok(small) = U64Small::try_from(u) {
                    Ok(small.into())
                } else {
                    Ok(self.add_lazy_obj(lazy.clone())?.into())
                }
            }
            ScValType::I64 => {
                let i = lazy.as_i64().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                if let Ok(small) = I64Small::try_from(i) {
                    Ok(small.into())
                } else {
                    Ok(self.add_lazy_obj(lazy.clone())?.into())
                }
            }
            ScValType::Timepoint => {
                let tp = lazy.as_timepoint().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                if let Ok(small) = TimepointSmall::try_from(*tp) {
                    Ok(small.into())
                } else {
                    Ok(self.add_lazy_obj(lazy.clone())?.into())
                }
            }
            ScValType::Duration => {
                let d = lazy.as_duration().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                if let Ok(small) = DurationSmall::try_from(*d) {
                    Ok(small.into())
                } else {
                    Ok(self.add_lazy_obj(lazy.clone())?.into())
                }
            }
            ScValType::U128 => {
                let u = lazy.as_u128().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                let val = int128_helpers::u128_from_pieces(u.hi(), u.lo());
                if let Ok(small) = U128Small::try_from(val) {
                    Ok(small.into())
                } else {
                    Ok(self.add_lazy_obj(lazy.clone())?.into())
                }
            }
            ScValType::I128 => {
                let i = lazy.as_i128().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                let val = int128_helpers::i128_from_pieces(i.hi(), i.lo());
                if let Ok(small) = I128Small::try_from(val) {
                    Ok(small.into())
                } else {
                    Ok(self.add_lazy_obj(lazy.clone())?.into())
                }
            }
            ScValType::U256 => {
                let u = lazy.as_u256().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                let val = u256_from_pieces(u.hi_hi(), u.hi_lo(), u.lo_hi(), u.lo_lo());
                if let Ok(small) = U256Small::try_from(val) {
                    Ok(small.into())
                } else {
                    Ok(self.add_lazy_obj(lazy.clone())?.into())
                }
            }
            ScValType::I256 => {
                let i = lazy.as_i256().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                let val = i256_from_pieces(i.hi_hi(), i.hi_lo(), i.lo_hi(), i.lo_lo());
                if let Ok(small) = I256Small::try_from(val) {
                    Ok(small.into())
                } else {
                    Ok(self.add_lazy_obj(lazy.clone())?.into())
                }
            }
            ScValType::Symbol => {
                // Try small symbol first (up to 9 chars)
                let lazy_sym = lazy.as_symbol().ok_or_else(|| {
                    HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                })?;
                let sym_bytes = lazy_sym.as_bytes();
                if let Ok(small) = SymbolSmall::try_from_bytes(sym_bytes) {
                    Ok(small.into())
                } else {
                    // Large symbol — create lazy host object
                    Ok(self.add_lazy_obj(lazy.clone())?.into())
                }
            }
            // All other object types: Vec, Map, Bytes, String, Address,
            // ContractInstance, LedgerKeyNonce — wrap as lazy
            ScValType::Vec
            | ScValType::Map
            | ScValType::Bytes
            | ScValType::String
            | ScValType::Address
            | ScValType::ContractInstance
            | ScValType::LedgerKeyNonce => {
                Ok(self.add_lazy_obj(lazy.clone())?.into())
            }
            // LedgerKeyContractInstance is a special value, not an object
            ScValType::LedgerKeyContractInstance => {
                Ok(ScVal::LedgerKeyContractInstance.try_into_val(self).map_err(
                    |cerr| self.error(cerr, "failed to convert LedgerKeyContractInstance", &[]),
                )?)
            }
        }
    }

    pub(crate) fn from_host_obj(&self, ob: impl Into<Object>) -> Result<ScValObject, HostError> {
        unsafe {
            let objref: Object = ob.into();
            let lazy = self.get_lazy_obj(objref)?;

            // Check for muxed address restriction in storage key context
            if *self.try_borrow_storage_key_conversion_active()? {
                if let Some(addr) = lazy.as_address() {
                    let scval = ScVal::try_from(&lazy).map_err(|_| {
                        HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
                    })?;
                    if let ScVal::Address(ScAddress::MuxedAccount(_)) = &scval {
                        return Err(self.err(
                            ScErrorType::Storage,
                            ScErrorCode::InvalidInput,
                            "muxed addresses should not be used in the storage keys",
                            &[objref.to_val()],
                        ));
                    }
                }
            }

            let scval = ScVal::try_from(&lazy).map_err(|_| {
                HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
            })?;
            Ok(ScValObject::unchecked_from_val(scval))
        }
    }

    pub(crate) fn to_host_obj(&self, ob: &ScValObjRef<'_>) -> Result<Object, HostError> {
        let val: &ScVal = (*ob).into();
        self.add_obj_from_scval(val.clone())
    }

    pub(crate) fn non_muxed_sc_address_to_strkey(
        &self,
        addr: &ScAddress,
    ) -> Result<String, HostError> {
        // Approximate the strkey encoding cost with two vector allocations:
        // one for the payload size (32-byte key/hash + 3 bytes for
        // version/checksum) and another one for the base32 encoding of
        // the payload.
        const PAYLOAD_LEN: u64 = 32 + 3;
        Vec::<u8>::charge_bulk_init_cpy(PAYLOAD_LEN + (PAYLOAD_LEN * 8).div_ceil(5), self)?;
        let strkey = match addr {
            ScAddress::Account(acc_id) => {
                let AccountId(PublicKey::PublicKeyTypeEd25519(Uint256(ed25519))) = acc_id;
                stellar_strkey::Strkey::PublicKeyEd25519(stellar_strkey::ed25519::PublicKey(
                    ed25519.metered_clone(self)?,
                ))
            }
            ScAddress::Contract(ContractId(Hash(h))) => {
                stellar_strkey::Strkey::Contract(stellar_strkey::Contract(h.metered_clone(self)?))
            }
            _ => {
                return Err(self.err(
                    ScErrorType::Object,
                    ScErrorCode::InternalError,
                    "Unexpected ScAddress type for strkey encoding",
                    &[],
                ))
            }
        };
        Ok(strkey.to_string())
    }

    pub(crate) fn muxed_sc_address_to_strkey(
        &self,
        muxed_addr: &MuxedScAddress,
    ) -> Result<String, HostError> {
        // Approximate the strkey encoding cost for muxed accounts
        // (32-byte key + 8-byte id + 3 bytes for version/checksum)
        const MUXED_PAYLOAD_LEN: u64 = 32 + 8 + 3;
        Vec::<u8>::charge_bulk_init_cpy(
            MUXED_PAYLOAD_LEN + (MUXED_PAYLOAD_LEN * 8).div_ceil(5),
            self,
        )?;
        match &muxed_addr.0 {
            ScAddress::MuxedAccount(muxed_account) => {
                let strkey = stellar_strkey::Strkey::MuxedAccountEd25519(
                    stellar_strkey::ed25519::MuxedAccount {
                        id: muxed_account.id,
                        ed25519: muxed_account.ed25519.0.metered_clone(self)?,
                    },
                );
                Ok(strkey.to_string())
            }
            _ => Err(self.err(
                ScErrorType::Object,
                ScErrorCode::InternalError,
                "MuxedAddressObject is used to represent a regular address",
                &[],
            )),
        }
    }

    /// Parses a strkey from a String or Bytes object into an ScAddress.
    ///
    /// When `allow_muxed` is true, accepts Account, Contract, and MuxedAccount strkeys.
    /// When `allow_muxed` is false, only accepts Account and Contract strkeys.
    pub(crate) fn strkey_to_scaddress(
        &self,
        strkey_obj: Val,
        allow_muxed: bool,
    ) -> Result<ScAddress, HostError> {
        let strkey_obj = Object::try_from(strkey_obj).map_err(|_| {
            self.err(
                ScErrorType::Value,
                ScErrorCode::UnexpectedType,
                "strkey is not an object",
                &[strkey_obj],
            )
        })?;

        let lazy = self.get_lazy_obj(strkey_obj)?;
        let scval = ScVal::try_from(&lazy).map_err(|_| {
            HostError::from((ScErrorType::Value, ScErrorCode::InternalError))
        })?;
        let key: Vec<u8> = match &scval {
            ScVal::Bytes(b) => b.as_slice().to_vec(),
            ScVal::String(s) => s.as_slice().to_vec(),
            _ => {
                return Err(self.err(
                    ScErrorType::Value,
                    ScErrorCode::UnexpectedType,
                    "strkey is not a string or bytes object",
                    &[strkey_obj.to_val()],
                ));
            }
        };
        let key: &[u8] = &key;

        {
            // Expected strkey lengths:
            // - Account/Contract: PAYLOAD_LEN = 32 + 3 = 35 bytes → 56 chars in base32
            // - Muxed account: MUXED_PAYLOAD_LEN = 32 + 8 + 3 = 43 bytes → 69 chars in base32
            const PAYLOAD_LEN: u64 = 32 + 3;
            const MUXED_PAYLOAD_LEN: u64 = 32 + 8 + 3;
            let expected_key_len = (PAYLOAD_LEN * 8).div_ceil(5);
            let expected_muxed_key_len = (MUXED_PAYLOAD_LEN * 8).div_ceil(5);
            let key_len = key.len() as u64;

            let (valid_length, payload_len) = if allow_muxed {
                if key_len == expected_key_len {
                    (true, PAYLOAD_LEN)
                } else if key_len == expected_muxed_key_len {
                    (true, MUXED_PAYLOAD_LEN)
                } else {
                    (false, 0)
                }
            } else {
                (key_len == expected_key_len, PAYLOAD_LEN)
            };
            if !valid_length {
                return Err(self.err(
                    ScErrorType::Value,
                    ScErrorCode::InvalidInput,
                    "unexpected strkey length",
                    &[strkey_obj.to_val()],
                ));
            }

            // Charge for the key copy to string.
            Vec::<u8>::charge_bulk_init_cpy(key_len, self)?;
            let key_str = String::from_utf8_lossy(key);
            // Approximate the decoding cost as two vector allocations for the
            // payload length (the strkey library does one extra copy).
            Vec::<u8>::charge_bulk_init_cpy(payload_len * 2, self)?;
            let strkey = stellar_strkey::Strkey::from_string(&key_str).map_err(|_| {
                self.err(
                    ScErrorType::Value,
                    ScErrorCode::InvalidInput,
                    "couldn't process the string as strkey",
                    &[strkey_obj.to_val()],
                )
            })?;
            match strkey {
                stellar_strkey::Strkey::PublicKeyEd25519(pk) => Ok(ScAddress::Account(AccountId(
                    PublicKey::PublicKeyTypeEd25519(Uint256(pk.0)),
                ))),
                stellar_strkey::Strkey::Contract(c) => {
                    Ok(ScAddress::Contract(ContractId(Hash(c.0))))
                }
                stellar_strkey::Strkey::MuxedAccountEd25519(m) if allow_muxed => {
                    Ok(ScAddress::MuxedAccount(MuxedEd25519Account {
                        id: m.id,
                        ed25519: Uint256(m.ed25519),
                    }))
                }
                _ => Err(self.err(
                    ScErrorType::Value,
                    ScErrorCode::InvalidInput,
                    "incorrect strkey type",
                    &[strkey_obj.to_val()],
                )),
            }
        }
    }
}
