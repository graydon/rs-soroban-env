use soroban_env_common::{CheckedEnv, EnvBase};

use crate::{
    budget::Budget,
    host::metered_map::MeteredOrdMap,
    storage::{AccessType, Footprint, Storage},
    xdr, Host, HostError, RawVal,
};

#[test]
fn check_account_exists() -> Result<(), HostError> {
    let id0 = [0; 32];
    let id1 = [1; 32]; // declared, but not in storage
    let id2 = [2; 32]; // not declared
    let acc_id0 = xdr::Uint256(id0.clone());
    let acc_id1 = xdr::Uint256(id1.clone());
    let acc_id2 = xdr::Uint256(id2.clone());
    let (lk0, le0) = Host::test_account_ledger_key_entry_pair(acc_id0);
    let (lk1, _le1) = Host::test_account_ledger_key_entry_pair(acc_id1);
    let (_lk2, _le2) = Host::test_account_ledger_key_entry_pair(acc_id2);

    let budget = Budget::default();
    let mut footprint = Footprint::default();
    footprint.record_access(&lk0, AccessType::ReadOnly).unwrap();
    footprint.record_access(&lk1, AccessType::ReadOnly).unwrap();

    let mut map = im_rc::OrdMap::default();
    map.insert(lk0, Some(le0));
    let storage = Storage::with_enforcing_footprint_and_map(
        footprint,
        MeteredOrdMap {
            budget: budget.clone(),
            map,
        },
    );

    let host = Host::with_storage_and_budget(storage, budget.clone());
    let obj0 = host.bytes_new_from_slice(&id0)?;
    let obj1 = host.bytes_new_from_slice(&id1)?;
    let obj2 = host.bytes_new_from_slice(&id2)?;
    // declared and exists
    assert_eq!(
        host.account_exists(obj0)?.get_payload(),
        RawVal::from_bool(true).get_payload()
    );
    // declared but does not exist
    assert_eq!(
        host.account_exists(obj1)?.get_payload(),
        RawVal::from_bool(false).get_payload()
    );
    // not declared
    assert!(HostError::result_matches_err_status(
        host.account_exists(obj2),
        xdr::ScHostStorageErrorCode::AccessToUnknownEntry
    ));
    Ok(())
}
