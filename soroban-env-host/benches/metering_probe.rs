// Metering-ratio probe benchmark.
//
// This benchmark is a framework for exploring edge cases in the Soroban host's
// metering system. It runs a "probe" -- a user-defined sequence of host Env API
// calls -- and measures both the *metered* virtual CPU cost (as charged by the
// budget system) and the *real* cost (either hardware CPU instructions via
// perf/rusage, or wall-clock nanoseconds). It then reports the ratio of
// metered-to-real cost. A well-calibrated host function should have a
// consistent, roughly-constant ratio; a mis-calibrated one will show a ratio
// that deviates significantly from the norm, indicating that the metering
// model under- or over-charges for the actual work.
//
// The benchmark is deliberately organized so that the probe subroutine
// (`fn probe`) is a single, self-contained function that a future LLM agent
// can replace or mutate to explore pathological inputs and discover metering
// holes without having to understand or modify the measurement harness.
//
// Usage:
//   # Measure using real CPU instructions (default, Linux perf / macOS rusage):
//   cargo bench --features bench --bench metering_probe -- --nocapture
//
//   # Measure using wall-clock time instead:
//   MODE=time cargo bench --features bench --bench metering_probe -- --nocapture
//
//   # Control the number of repetitions (default 20):
//   REPS=50 cargo bench --features bench --bench metering_probe -- --nocapture
//
//   # Control the input-size parameter passed to the probe (default 100):
//   INPUT=500 cargo bench --features bench --bench metering_probe -- --nocapture

use soroban_bench_utils::{tracking_allocator::AllocationGroupToken, HostTracker};
use soroban_env_host::{
    budget::AsBudget,
    xdr::ContractCostType,
    Env, Host, HostError, LedgerInfo,
};
use std::io::Write;
use tabwriter::{Alignment, TabWriter};

// =============================================================================
// Probe definition — THIS IS THE FUNCTION AN LLM SHOULD REPLACE OR MUTATE.
//
// The probe receives:
//   - `host`: a fresh Host with unlimited budget (metering is still tracked)
//   - `input`: a size parameter that the probe can use however it likes
//
// It should perform one or more host Env API calls and return Ok(()).
// The harness will measure the real cost of everything that happens inside
// this function and compare it to the metered cost the budget system charged.
//
// Guidelines for writing probes:
//   - Focus on a single host function or a tight combination.
//   - Vary the `input` parameter to explore how cost scales.
//   - Try pathological or adversarial inputs (e.g. worst-case hash collisions,
//     maximally-nested structures, large-then-small sequences, etc.)
//   - The function can call any method on `Host` that implements `Env`.
// =============================================================================

/// A single metered action to probe. Replace the body of this function to
/// explore different host functions and edge cases.
fn probe(host: &Host, input: u64) -> Result<(), HostError> {
    // --- Example probe: exercises bytes, vec, map, and crypto APIs ---

    // 1. Build a Bytes object of size `input` by repeated push.
    let mut bytes_obj = host.bytes_new()?;
    for i in 0..input {
        bytes_obj = host.bytes_push(bytes_obj, (i as u32 % 256).into())?;
    }

    // 2. Hash the bytes with SHA-256.
    let _hash = host.compute_hash_sha256(bytes_obj)?;

    // 3. Build a Vec of u32 vals of length `input`.
    let mut vec_obj = host.vec_new()?;
    for i in 0..input {
        vec_obj = host.vec_push_back(vec_obj, (i as u32).into())?;
    }

    // 4. Binary-search for the middle element.
    let mid = (input / 2) as u32;
    let _idx = host.vec_binary_search(vec_obj, mid.into())?;

    // 5. Build a Map with `input` entries.
    let mut map_obj = host.map_new()?;
    for i in 0..input {
        map_obj = host.map_put(map_obj, (i as u32).into(), (i as u32).into())?;
    }

    // 6. Look up every key in the map.
    for i in 0..input {
        let _val = host.map_get(map_obj, (i as u32).into())?;
    }

    Ok(())
}

// =============================================================================
// Measurement harness — stable infrastructure, not intended for mutation.
// =============================================================================

/// Which real-cost metric to report.
#[derive(Clone, Copy, Debug)]
enum Mode {
    /// Hardware CPU instructions (perf on Linux, rusage on macOS).
    CpuInsns,
    /// Wall-clock nanoseconds.
    WallTime,
}

fn parse_mode() -> Mode {
    match std::env::var("MODE").ok().as_deref() {
        Some("time") | Some("wall") | Some("ns") => Mode::WallTime,
        _ => Mode::CpuInsns,
    }
}

fn parse_u64_env(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

fn make_host() -> Host {
    let host = Host::default();
    host.set_ledger_info(LedgerInfo {
        protocol_version: Host::current_test_protocol(),
        ..Default::default()
    })
    .unwrap();
    // Reset to unlimited so charges are tracked but never rejected.
    host.as_budget().reset_unlimited().unwrap();
    host.as_budget().reset_fuel_config().unwrap();
    host
}

/// A single trial result.
#[derive(Clone, Debug)]
struct Trial {
    input: u64,
    metered_cpu: u64,
    real_cpu_insns: u64,
    real_time_ns: u64,
}

impl Trial {
    fn ratio(&self, mode: Mode) -> f64 {
        let real = match mode {
            Mode::CpuInsns => self.real_cpu_insns,
            Mode::WallTime => self.real_time_ns,
        };
        if real == 0 {
            return f64::NAN;
        }
        self.metered_cpu as f64 / real as f64
    }
}

/// Runs the probe once and returns a trial measurement.
fn run_trial(input: u64) -> Trial {
    let host = make_host();

    let mut alloc_group_token =
        AllocationGroupToken::register().expect("failed to register allocation group");

    // --- Measure ---
    let mut ht = HostTracker::new();
    ht.start(Some(&mut alloc_group_token));

    // Actually run the probe.
    probe(&host, input).expect("probe returned an error");

    let (cpu_insns, _mem_bytes, time_nsecs) = ht.stop();

    // Read the metered cost the budget system charged.
    let metered_cpu = host
        .as_budget()
        .get_cpu_insns_consumed()
        .expect("get_cpu_insns_consumed");

    Trial {
        input,
        metered_cpu,
        real_cpu_insns: cpu_insns,
        real_time_ns: time_nsecs,
    }
}

/// Pretty-print the results.
fn report(mode: Mode, trials: &[Trial]) {
    let real_label = match mode {
        Mode::CpuInsns => "real_cpu_insns",
        Mode::WallTime => "real_time_ns",
    };

    use thousands::Separable;

    let mut tw = TabWriter::new(vec![])
        .padding(3)
        .alignment(Alignment::Right);

    writeln!(
        &mut tw,
        "input\tmetered_cpu\t{}\tratio (metered/real)",
        real_label
    )
    .unwrap();
    writeln!(&mut tw, "-----\t-----------\t{}\t--------------------",
        "-".repeat(real_label.len())).unwrap();

    for t in trials {
        let real = match mode {
            Mode::CpuInsns => t.real_cpu_insns,
            Mode::WallTime => t.real_time_ns,
        };
        let ratio = t.ratio(mode);
        writeln!(
            &mut tw,
            "{}\t{}\t{}\t{:.4}",
            t.input.separate_with_commas(),
            t.metered_cpu.separate_with_commas(),
            real.separate_with_commas(),
            ratio,
        )
        .unwrap();
    }
    tw.flush().unwrap();
    eprintln!("\n{}", String::from_utf8(tw.into_inner().unwrap()).unwrap());

    // Summary statistics on the ratio.
    let ratios: Vec<f64> = trials.iter().map(|t| t.ratio(mode)).collect();
    let mean = ratios.iter().sum::<f64>() / ratios.len() as f64;
    let variance = ratios.iter().map(|r| (r - mean).powi(2)).sum::<f64>() / ratios.len() as f64;
    let stddev = variance.sqrt();
    let min = ratios.iter().cloned().reduce(f64::min).unwrap_or(0.0);
    let max = ratios.iter().cloned().reduce(f64::max).unwrap_or(0.0);

    eprintln!("Ratio summary (metered_cpu / {}):", real_label);
    eprintln!("  mean   = {:.4}", mean);
    eprintln!("  stddev = {:.4}", stddev);
    eprintln!("  min    = {:.4}", min);
    eprintln!("  max    = {:.4}", max);
    eprintln!("  spread = {:.4} (max/min)", if min > 0.0 { max / min } else { f64::NAN });
    eprintln!();

    // Also break down per-cost-type charges so the user can see where budget
    // was spent.
    eprintln!("Per-cost-type metered charges (from last trial):");
    if let Some(last) = trials.last() {
        let host = make_host();
        host.as_budget().reset_unlimited().unwrap();
        probe(&host, last.input).expect("probe re-run for breakdown");
        let mut tw2 = TabWriter::new(vec![])
            .padding(3)
            .alignment(Alignment::Right);
        writeln!(&mut tw2, "cost_type\titerations\tcpu_insns\tmem_bytes").unwrap();
        for ct in ContractCostType::VARIANTS {
            if let Ok(tracker) = host.as_budget().get_tracker(ct) {
                if tracker.iterations > 0 {
                    writeln!(
                        &mut tw2,
                        "{:?}\t{}\t{}\t{}",
                        ct,
                        tracker.iterations.separate_with_commas(),
                        tracker.cpu.separate_with_commas(),
                        tracker.mem.separate_with_commas(),
                    )
                    .unwrap();
                }
            }
        }
        tw2.flush().unwrap();
        eprintln!("{}", String::from_utf8(tw2.into_inner().unwrap()).unwrap());
    }
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
fn main() -> std::io::Result<()> {
    let mode = parse_mode();
    let reps = parse_u64_env("REPS", 20);
    let input_lo = parse_u64_env("INPUT_LO", 10);
    let input_hi = parse_u64_env("INPUT_HI", 0);
    let fixed_input = parse_u64_env("INPUT", 0);

    eprintln!("=== Metering Probe Benchmark ===");
    eprintln!("Mode: {:?}", mode);

    let trials: Vec<Trial> = if input_hi > 0 {
        // Sweep mode: vary input from INPUT_LO to INPUT_HI in `reps` steps.
        let step = ((input_hi - input_lo) as f64 / (reps.max(1) - 1) as f64).ceil() as u64;
        (0..reps)
            .map(|i| {
                let inp = input_lo + i * step;
                let inp = inp.min(input_hi);
                eprintln!("  trial {}/{}: input={}", i + 1, reps, inp);
                run_trial(inp)
            })
            .collect()
    } else if fixed_input > 0 {
        // Fixed-input mode: same input repeated `reps` times.
        (0..reps)
            .map(|i| {
                eprintln!("  trial {}/{}: input={}", i + 1, reps, fixed_input);
                run_trial(fixed_input)
            })
            .collect()
    } else {
        // Default: geometric sweep from 10 to ~10000.
        let base: f64 = (10000.0_f64 / 10.0).powf(1.0 / (reps.max(1) - 1) as f64);
        (0..reps)
            .map(|i| {
                let inp = (10.0 * base.powi(i as i32)).round() as u64;
                eprintln!("  trial {}/{}: input={}", i + 1, reps, inp);
                run_trial(inp)
            })
            .collect()
    };

    report(mode, &trials);
    Ok(())
}
