#![no_std]
use soroban_sdk::{contract, contractimpl, contracterror, Val, Error};

#[contract]
pub struct Contract;

#[contracterror]
#[derive(Copy,Clone)]
pub enum Eek
{
    BADNESS = 12345
}

#[contractimpl]
impl Contract {
    pub fn err_eek() -> Result<(), Eek> {
        Err(Eek::BADNESS)
    }

    pub fn err_err() -> Result<(), Error> {
        let e: Error = Error::from_contract_error(12345).into();
        Err(e)
    }

    pub fn ok_err() -> Result<Error, Eek> {
        let e: Error = Error::from_contract_error(12345).into();
        Ok(e)
    }

    pub fn ok_val_err() -> Result<Val, Eek> {
        let v: Val = Error::from_contract_error(12345).into();
        Ok(v)
    }

    pub fn ok_val() -> Result<(), Error> {
        Ok(())
    }

    pub fn accept(_v: Val) -> Result<(), Error> {
        Ok(())
    }
}
