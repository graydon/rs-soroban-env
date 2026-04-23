use std::hint::black_box;

use crate::{
    cost_runner::{CostRunner, CostType},
    xdr::ContractCostType::VisitObject,
    Object,
};

pub struct VisitObjectRun;

impl CostRunner for VisitObjectRun {
    const COST_TYPE: CostType = CostType::Contract(VisitObject);

    const RUN_ITERATIONS: u64 = 1000;

    type SampleType = Vec<Object>;

    type RecycledType = Self::SampleType;

    fn run_iter(host: &crate::Host, iter: u64, sample: Self::SampleType) -> Self::RecycledType {
        let _ = black_box(
            host.get_lazy_obj(sample[iter as usize % sample.len()])
                .unwrap(),
        );
        black_box(sample)
    }

    fn run_baseline_iter(
        host: &crate::Host,
        _iter: u64,
        sample: Self::SampleType,
    ) -> Self::RecycledType {
        black_box(host.charge_budget(VisitObject, None).unwrap());
        black_box(sample)
    }
}
