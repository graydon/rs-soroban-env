pub(crate) mod diagnostic;
mod internal;
pub(crate) mod system_events;

pub(crate) use internal::InternalEventsBuffer;
// expose them as pub use for benches
pub use internal::{InternalContractEvent, InternalEvent};
use soroban_env_common::{xdr::ContractEventType, RawVal, VecObject};

use crate::{budget::AsBudget, Host, HostError};

/// The external representation of a host event.
// TODO: optimize storage on this to use pools / bumpalo / etc.
#[derive(Clone, Debug)]
pub struct HostEvent {
    pub event: Event,
    // failed_call keeps track of if the call this event was emitted in failed
    pub failed_call: bool,
}

#[derive(Clone, Debug)]
pub enum Event {
    Contract(crate::xdr::ContractEvent),
    // StructuredDebug should not affect metering
    StructuredDebug(crate::xdr::ContractEvent),
}

/// The external representation of events in the chronological order.
#[derive(Clone, Debug, Default)]
pub struct Events(pub Vec<HostEvent>);

// Maximum number of topics in a `ContractEvent`. This applies to both
// `Contract` and `System` types of contract events.
pub(crate) const CONTRACT_EVENT_TOPICS_LIMIT: usize = 4;
// Maximum number of bytes in a topic `Bytes`.
pub(crate) const TOPIC_BYTES_LENGTH_LIMIT: usize = 64;

impl Host {
    pub(crate) fn with_events_mut<F, U>(&self, f: F) -> Result<U, HostError>
    where
        F: FnOnce(&mut InternalEventsBuffer) -> Result<U, HostError>,
    {
        f(&mut self.0.events.borrow_mut())
    }

    pub fn get_events(&self) -> Result<Events, HostError> {
        self.0.events.borrow().externalize(self)
    }

    // Records a contract event.
    pub(crate) fn record_contract_event(
        &self,
        type_: ContractEventType,
        topics: VecObject,
        data: RawVal,
    ) -> Result<(), HostError> {
        self.validate_contract_event_topics(topics)?;
        let ce = InternalContractEvent {
            type_,
            contract_id: self.bytesobj_from_internal_contract_id()?,
            topics,
            data,
        };
        self.with_events_mut(|events| {
            Ok(events.record(InternalEvent::Contract(ce), self.as_budget()))
        })?
    }
}
