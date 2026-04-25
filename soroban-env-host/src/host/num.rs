#[macro_export]
macro_rules! impl_wrapping_obj_from_num {
    (obj_from_u64, $hot: ty, $obj: ty, $num: ty) => {
        fn obj_from_u64(&self, _vmcaller: &mut VmCaller<Host>, u: $num) -> Result<$obj, HostError> {
            self.add_obj_u64(u)
        }
    };
    (obj_from_i64, $hot: ty, $obj: ty, $num: ty) => {
        fn obj_from_i64(&self, _vmcaller: &mut VmCaller<Host>, u: $num) -> Result<$obj, HostError> {
            self.add_obj_i64(u)
        }
    };
    (timepoint_obj_from_u64, $hot: ty, $obj: ty, $num: ty) => {
        fn timepoint_obj_from_u64(
            &self,
            _vmcaller: &mut VmCaller<Host>,
            u: $num,
        ) -> Result<$obj, HostError> {
            self.add_obj_timepoint($crate::xdr::TimePoint::from(u))
        }
    };
    (duration_obj_from_u64, $hot: ty, $obj: ty, $num: ty) => {
        fn duration_obj_from_u64(
            &self,
            _vmcaller: &mut VmCaller<Host>,
            u: $num,
        ) -> Result<$obj, HostError> {
            self.add_obj_duration($crate::xdr::Duration::from(u))
        }
    };
}

#[macro_export]
macro_rules! impl_wrapping_obj_to_num {
    (obj_to_u64, $data: ty, $obj: ty, $num: ty) => {
        fn obj_to_u64(&self, _vmcaller: &mut VmCaller<Host>, obj: $obj) -> Result<$num, HostError> {
            let lazy = self.get_lazy_obj($crate::host_object::to_object(&obj)?)?;
            Ok(lazy.as_u64().ok_or_else(|| {
                $crate::HostError::from((
                    $crate::xdr::ScErrorType::Object,
                    $crate::xdr::ScErrorCode::UnexpectedType,
                ))
            })?)
        }
    };
    (obj_to_i64, $data: ty, $obj: ty, $num: ty) => {
        fn obj_to_i64(&self, _vmcaller: &mut VmCaller<Host>, obj: $obj) -> Result<$num, HostError> {
            let lazy = self.get_lazy_obj($crate::host_object::to_object(&obj)?)?;
            Ok(lazy.as_i64().ok_or_else(|| {
                $crate::HostError::from((
                    $crate::xdr::ScErrorType::Object,
                    $crate::xdr::ScErrorCode::UnexpectedType,
                ))
            })?)
        }
    };
    (timepoint_obj_to_u64, $data: ty, $obj: ty, $num: ty) => {
        fn timepoint_obj_to_u64(
            &self,
            _vmcaller: &mut VmCaller<Host>,
            obj: $obj,
        ) -> Result<$num, HostError> {
            let lazy = self.get_lazy_obj($crate::host_object::to_object(&obj)?)?;
            let tp = lazy.as_timepoint().ok_or_else(|| {
                $crate::HostError::from((
                    $crate::xdr::ScErrorType::Object,
                    $crate::xdr::ScErrorCode::UnexpectedType,
                ))
            })?;
            Ok(*tp)
        }
    };
    (duration_obj_to_u64, $data: ty, $obj: ty, $num: ty) => {
        fn duration_obj_to_u64(
            &self,
            _vmcaller: &mut VmCaller<Host>,
            obj: $obj,
        ) -> Result<$num, HostError> {
            let lazy = self.get_lazy_obj($crate::host_object::to_object(&obj)?)?;
            let d = lazy.as_duration().ok_or_else(|| {
                $crate::HostError::from((
                    $crate::xdr::ScErrorType::Object,
                    $crate::xdr::ScErrorCode::UnexpectedType,
                ))
            })?;
            Ok(*d)
        }
    };
}

#[macro_export]
macro_rules! impl_bignum_host_fns {
    (@core $host: ident, $lhs_val: ident, $rhs_val: ident, $maybe_res: ident,
           $method: ident, $num: ty, $cost: ident) => {
        $host.charge_budget(ContractCostType::$cost, None)?;
        let lhs: $num = $lhs_val.to_val().try_into_val($host)?;
        let rhs = $rhs_val.to_val().try_into_val($host)?;
        $maybe_res = lhs.$method(rhs);
    };
    ($host_fn: ident, $method: ident, $num: ty, $valty: ty, $operand_valty: ty, $cost: ident) => {
        fn $host_fn(
            &self,
            _vmcaller: &mut VmCaller<Self::VmUserState>,
            lhs_val: $valty,
            rhs_val: $operand_valty,
        ) -> Result<$valty, Self::Error> {
            let host = self;
            let maybe_res: Option<$num>;
            impl_bignum_host_fns!(@core host, lhs_val, rhs_val, maybe_res,
                                         $method, $num, $cost);
            let res = maybe_res.ok_or_else(|| {
                host.err(
                    ScErrorType::Object,
                    ScErrorCode::ArithDomain,
                    "overflow has occurred",
                    &[lhs_val.to_val(), rhs_val.to_val()],
                )
            })?;
            Ok(res.try_into_val(host)?)
        }
    };
    ($host_fn: ident, $method: ident, $num: ty, $valty: ty, $operand_valty: ty, $cost: ident, checked) => {
        fn $host_fn(
            &self,
            _vmcaller: &mut VmCaller<Self::VmUserState>,
            lhs_val: $valty,
            rhs_val: $operand_valty,
        ) -> Result<Val, Self::Error> {
            let host = self;
            let maybe_res: Option<$num>;
            impl_bignum_host_fns!(@core host, lhs_val, rhs_val, maybe_res,
                                         $method, $num, $cost);
            match maybe_res {
                Some(res) => {
                    let v: $valty = res.try_into_val(host)?;
                    Ok(v.to_val())
                }
                None => Ok(Val::VOID.to_val()),
            }
        }
    };
}

#[macro_export]
macro_rules! impl_bls12_381_fr_arith_host_fns {
    ($host_fn: ident, $method: ident) => {
        fn $host_fn(
            &self,
            _vmcaller: &mut VmCaller<Self::VmUserState>,
            lhs: U256Val,
            rhs: U256Val,
        ) -> Result<U256Val, Self::Error> {
            let mut lhs = self.fr_from_u256val(lhs)?;
            let rhs = self.fr_from_u256val(rhs)?;
            self.$method(&mut lhs, &rhs)?;
            self.fr_to_u256val(lhs)
        }
    };
}

#[macro_export]
macro_rules! impl_bn254_fr_arith_host_fns {
    ($host_fn: ident, $method: ident) => {
        fn $host_fn(
            &self,
            _vmcaller: &mut VmCaller<Self::VmUserState>,
            lhs: U256Val,
            rhs: U256Val,
        ) -> Result<U256Val, Self::Error> {
            let mut lhs = self.bn254_fr_from_u256val(lhs)?;
            let rhs = self.bn254_fr_from_u256val(rhs)?;
            self.$method(&mut lhs, &rhs)?;
            self.bn254_fr_to_u256val(lhs)
        }
    };
}
