use anyhow::{Error, Result};
use zkevm_opcode_defs::bn254::bn256::{Fq, Fq12, Fq2, G1Affine, G2Affine};
use zkevm_opcode_defs::bn254::ff::{Field, PrimeField};
use zkevm_opcode_defs::bn254::CurveAffine;
pub use zkevm_opcode_defs::sha2::Digest;
use zkevm_opcode_defs::ethereum_types::U256;

use super::*;

// NOTE: We need x1, y1, x2, y2, x3, y3: 
pub const MEMORY_READS_PER_CYCLE: usize = 6;
// NOTE: We need to specify the result of the pairing and the status of the operation
pub const MEMORY_WRITES_PER_CYCLE: usize = 2;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ECPairingRoundWitness {
    pub new_request: LogQuery,
    pub reads: [MemoryQuery; MEMORY_READS_PER_CYCLE],
    pub writes: [MemoryQuery; MEMORY_WRITES_PER_CYCLE],
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ECPairingPrecompile<const B: bool>;

impl<const B: bool> Precompile for ECPairingPrecompile<B> {
    type CycleWitness = ECPairingRoundWitness;

    fn execute_precompile<M: Memory>(
        &mut self,
        monotonic_cycle_counter: u32,
        query: LogQuery,
        memory: &mut M,
    ) -> (
        usize,
        Option<(Vec<MemoryQuery>, Vec<MemoryQuery>, Vec<Self::CycleWitness>)>,
    ) {
        const NUM_ROUNDS: usize = 1;

        // read the parameters
        let precompile_call_params = query;
        let params = precompile_abi_in_log(precompile_call_params);
        let timestamp_to_read = precompile_call_params.timestamp;
        let timestamp_to_write = Timestamp(timestamp_to_read.0 + 1); // our default timestamping agreement

        let mut current_read_location = MemoryLocation {
            memory_type: MemoryType::Heap, // we default for some value, here it's not that important
            page: MemoryPage(params.memory_page_to_read),
            index: MemoryIndex(params.input_memory_offset),
        };

        // we assume that we have
        // - x1 as U256 as a first coordinate of the first point (32 bytes)
        // - y1 as U256 as a second coordinate of the first point (32 bytes)
        // - x2 as U256 as a c0 component of first coordinate of the second point (32 bytes)
        // - y2 as U256 as a c1 component of first coordinate of the second point (32 bytes)
        // - x3 as U256 as a c0 component of second coordinate of the second point (32 bytes)
        // - y3 as U256 as a c1 component of second coordinate of the second point (32 bytes)

        // we do 8 queries per precompile
        let mut read_history = if B {
            Vec::with_capacity(MEMORY_READS_PER_CYCLE)
        } else {
            vec![]
        };
        let mut write_history = if B {
            Vec::with_capacity(MEMORY_WRITES_PER_CYCLE)
        } else {
            vec![]
        };

        let mut round_witness = ECPairingRoundWitness {
            new_request: precompile_call_params,
            reads: [MemoryQuery::empty(); MEMORY_READS_PER_CYCLE],
            writes: [MemoryQuery::empty(); MEMORY_WRITES_PER_CYCLE],
        };

        let mut read_idx = 0;

        let x1_query = MemoryQuery {
            timestamp: timestamp_to_read,
            location: current_read_location,
            value: U256::zero(),
            value_is_pointer: false,
            rw_flag: false,
        };
        let x1_query = memory.execute_partial_query(monotonic_cycle_counter, x1_query);
        let x1_value = x1_query.value;
        if B {
            round_witness.reads[read_idx] = x1_query;
            read_idx += 1;
            read_history.push(x1_query);
        }

        current_read_location.index.0 += 1;
        let y1_query = MemoryQuery {
            timestamp: timestamp_to_read,
            location: current_read_location,
            value: U256::zero(),
            value_is_pointer: false,
            rw_flag: false,
        };
        let y1_query = memory.execute_partial_query(monotonic_cycle_counter, y1_query);
        let y1_value = y1_query.value;
        if B {
            round_witness.reads[read_idx] = y1_query;
            read_idx += 1;
            read_history.push(y1_query);
        }

        current_read_location.index.0 += 1;
        let x2_query = MemoryQuery {
            timestamp: timestamp_to_read,
            location: current_read_location,
            value: U256::zero(),
            value_is_pointer: false,
            rw_flag: false,
        };
        let x2_query = memory.execute_partial_query(monotonic_cycle_counter, x2_query);
        let x2_value = x2_query.value;
        if B {
            round_witness.reads[read_idx] = x2_query;
            read_idx += 1;
            read_history.push(x2_query);
        }

        current_read_location.index.0 += 1;
        let y2_query = MemoryQuery {
            timestamp: timestamp_to_read,
            location: current_read_location,
            value: U256::zero(),
            value_is_pointer: false,
            rw_flag: false,
        };
        let y2_query = memory.execute_partial_query(monotonic_cycle_counter, y2_query);
        let y2_value = y2_query.value;
        if B {
            round_witness.reads[read_idx] = y2_query;
            read_idx += 1;
            read_history.push(y2_query);
        }

        current_read_location.index.0 += 1;
        let x3_query = MemoryQuery {
            timestamp: timestamp_to_read,
            location: current_read_location,
            value: U256::zero(),
            value_is_pointer: false,
            rw_flag: false,
        };
        let x3_query = memory.execute_partial_query(monotonic_cycle_counter, x3_query);
        let x3_value = x3_query.value;
        if B {
            round_witness.reads[read_idx] = x3_query;
            read_idx += 1;
            read_history.push(x3_query);
        }

        current_read_location.index.0 += 1;
        let y3_query = MemoryQuery {
            timestamp: timestamp_to_read,
            location: current_read_location,
            value: U256::zero(),
            value_is_pointer: false,
            rw_flag: false,
        };
        let y3_query = memory.execute_partial_query(monotonic_cycle_counter, y3_query);
        let y3_value = y3_query.value;
        if B {
            round_witness.reads[read_idx] = y3_query;
            read_history.push(y3_query);
        }

        // Performing multiplication
        let pairing_check = ecpairing_inner((x1_value, y1_value), (x2_value, y2_value), (x3_value, y3_value));

        if let Ok(result) = pairing_check {
            let mut write_location = MemoryLocation {
                memory_type: MemoryType::Heap, // we default for some value, here it's not that important
                page: MemoryPage(params.memory_page_to_write),
                index: MemoryIndex(params.output_memory_offset),
            };

            // Marking that the operation was successful
            let ok_marker = U256::one();
            let ok_or_err_query = MemoryQuery {
                timestamp: timestamp_to_write,
                location: write_location,
                value: ok_marker,
                value_is_pointer: false,
                rw_flag: true,
            };
            let ok_or_err_query =
                memory.execute_partial_query(monotonic_cycle_counter, ok_or_err_query);

            // Converting result to one if true and zero otherwise
            let mut output_value = U256::zero();
            if result {
                output_value = U256::one();
            }

            write_location.index.0 += 1;            
            let result_query = MemoryQuery {
                timestamp: timestamp_to_write,
                location: write_location,
                value: output_value,
                value_is_pointer: false,
                rw_flag: true,
            };
            let result_query = memory.execute_partial_query(monotonic_cycle_counter, result_query);

            if B {
                round_witness.writes[0] = ok_or_err_query;
                round_witness.writes[1] = result_query;
                write_history.push(ok_or_err_query);
                write_history.push(result_query);
            }
        } else {
            let mut write_location = MemoryLocation {
                memory_type: MemoryType::Heap, // we default for some value, here it's not that important
                page: MemoryPage(params.memory_page_to_write),
                index: MemoryIndex(params.output_memory_offset),
            };

            let err_marker = U256::zero();
            let ok_or_err_query = MemoryQuery {
                timestamp: timestamp_to_write,
                location: write_location,
                value: err_marker,
                value_is_pointer: false,
                rw_flag: true,
            };
            let ok_or_err_query =
                memory.execute_partial_query(monotonic_cycle_counter, ok_or_err_query);

            write_location.index.0 += 1;
            let empty_result = U256::zero();
            let result_query = MemoryQuery {
                timestamp: timestamp_to_write,
                location: write_location,
                value: empty_result,
                value_is_pointer: false,
                rw_flag: true,
            };
            let result_query = memory.execute_partial_query(monotonic_cycle_counter, result_query);

            if B {
                round_witness.writes[0] = ok_or_err_query;
                round_witness.writes[1] = result_query;
                write_history.push(ok_or_err_query);
                write_history.push(result_query);
            }
        }

        let witness = if B {
            Some((read_history, write_history, vec![round_witness]))
        } else {
            None
        };

        (NUM_ROUNDS, witness)
    }
}

/// This function checks whether the pairing of two points on the elliptic curve
/// produces one.
///
/// If the points are not on the curve or coordinates are not valid field elements,
/// the function will return an error.
pub fn ecpairing_inner(
    (x1, y1): (U256, U256),
    (x2, y2): (U256, U256),
    (x3, y3): (U256, U256),
) -> Result<bool> {
    // Converting coordinates to the finite field format
    // and validating that the conversion is successful
    let x1_field = Fq::from_str(x1.to_string().as_str()).ok_or(Error::msg("invalid x1"))?;
    let y1_field = Fq::from_str(y1.to_string().as_str()).ok_or(Error::msg("invalid y1"))?;
    let x2_field = Fq::from_str(x2.to_string().as_str()).ok_or(Error::msg("invalid x2"))?;
    let y2_field = Fq::from_str(y2.to_string().as_str()).ok_or(Error::msg("invalid y2"))?;
    let x3_field = Fq::from_str(x3.to_string().as_str()).ok_or(Error::msg("invalid x3"))?;
    let y3_field = Fq::from_str(y3.to_string().as_str()).ok_or(Error::msg("invalid y3"))?;

    // Setting both points.
    // NOTE: If one of the points is zero, then both coordinates are zero,
    // which aligns with the from_xy_checked method implementation.
    let point_1 = G1Affine::from_xy_checked(x1_field, y1_field)?;

    let point_2_x = Fq2{
        c0: x2_field,
        c1: y2_field,
    };
    let point_2_y = Fq2{
        c0: x3_field,
        c1: y3_field,
    };
    let point_2 = G2Affine::from_xy_checked(point_2_x, point_2_y)?;

    // Calculating the pairing operation and returning
    let pairing = point_1.pairing_with(&point_2);
    Ok(pairing == Fq12::one())
}

pub fn ecpairing_function<M: Memory, const B: bool>(
    monotonic_cycle_counter: u32,
    precompile_call_params: LogQuery,
    memory: &mut M,
) -> (
    usize,
    Option<(Vec<MemoryQuery>, Vec<MemoryQuery>, Vec<ECPairingRoundWitness>)>,
) {
    let mut processor = ECPairingPrecompile::<B>;
    processor.execute_precompile(monotonic_cycle_counter, precompile_call_params, memory)
}
