use std::str::FromStr;

use anyhow::{Error, Result};
use zkevm_opcode_defs::bn254::bn256::{Fq, Fr, G1Affine};
use zkevm_opcode_defs::bn254::ff::PrimeField;
use zkevm_opcode_defs::bn254::{CurveAffine, CurveProjective};
use zkevm_opcode_defs::ethereum_types::U256;
pub use zkevm_opcode_defs::sha2::Digest;

use super::*;

// NOTE: We need x1, y1, and s: two coordinates of the point and the scalar
pub const MEMORY_READS_PER_CYCLE: usize = 3;
// NOTE: We need to specify the result of the multiplication and the status of the operation
pub const MEMORY_WRITES_PER_CYCLE: usize = 3;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ECMulRoundWitness {
    pub new_request: LogQuery,
    pub reads: [MemoryQuery; MEMORY_READS_PER_CYCLE],
    pub writes: [MemoryQuery; MEMORY_WRITES_PER_CYCLE],
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ECMulPrecompile<const B: bool>;

impl<const B: bool> Precompile for ECMulPrecompile<B> {
    type CycleWitness = ECMulRoundWitness;

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
        // - x1 as U256 as a first coordinate of the point (32 bytes)
        // - y1 as U256 as a second coordinate of the point (32 bytes)
        // - s as U256 as a scalar to multiply with (32 bytes)

        // we do 6 queries per precompile
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

        let mut round_witness = ECMulRoundWitness {
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
        let s_query = MemoryQuery {
            timestamp: timestamp_to_read,
            location: current_read_location,
            value: U256::zero(),
            value_is_pointer: false,
            rw_flag: false,
        };
        let s_query = memory.execute_partial_query(monotonic_cycle_counter, s_query);
        let s_value = s_query.value;
        if B {
            round_witness.reads[read_idx] = s_query;
            read_history.push(s_query);
        }

        // Performing multiplication
        let point_multiplied = ecmul_inner((x1_value, y1_value), s_value);

        if let Ok(point) = point_multiplied {
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

            // Converting resultant (x, y) into U256 format
            let (x, y) = point.into_xy_unchecked();
            let x = U256::from_str(format!("{}", x.into_repr()).as_str()).unwrap();
            let y = U256::from_str(format!("{}", y.into_repr()).as_str()).unwrap();

            // Writing resultant x coordinate
            write_location.index.0 += 1;

            let x_result_query = MemoryQuery {
                timestamp: timestamp_to_write,
                location: write_location,
                value: x,
                value_is_pointer: false,
                rw_flag: true,
            };
            let x_result_query = memory.execute_partial_query(monotonic_cycle_counter, x_result_query);

            // Writing resultant y coordinate
            write_location.index.0 += 1;

            let y_result_query = MemoryQuery {
                timestamp: timestamp_to_write,
                location: write_location,
                value: y,
                value_is_pointer: false,
                rw_flag: true,
            };
            let y_result_query = memory.execute_partial_query(monotonic_cycle_counter, y_result_query);

            if B {
                round_witness.writes[0] = ok_or_err_query;
                round_witness.writes[1] = x_result_query;
                round_witness.writes[2] = y_result_query;
                write_history.push(ok_or_err_query);
                write_history.push(x_result_query);
                write_history.push(y_result_query);
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
            let x_result_query = MemoryQuery {
                timestamp: timestamp_to_write,
                location: write_location,
                value: empty_result,
                value_is_pointer: false,
                rw_flag: true,
            };
            let x_result_query = memory.execute_partial_query(monotonic_cycle_counter, x_result_query);

            write_location.index.0 += 1;
            let empty_result = U256::zero();
            let y_result_query = MemoryQuery {
                timestamp: timestamp_to_write,
                location: write_location,
                value: empty_result,
                value_is_pointer: false,
                rw_flag: true,
            };
            let y_result_query = memory.execute_partial_query(monotonic_cycle_counter, y_result_query);

            if B {
                round_witness.writes[0] = ok_or_err_query;
                round_witness.writes[1] = x_result_query;
                round_witness.writes[2] = y_result_query;
                write_history.push(ok_or_err_query);
                write_history.push(x_result_query);
                write_history.push(y_result_query);
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

/// This function multiplies the point (x1,y1) by the scalar s on the BN254 curve.
/// It returns the result as a G1Affine point.
///
/// If the points are not on the curve or coordinates are not valid field elements,
/// the function will return an error.
pub fn ecmul_inner((x1, y1): (U256, U256), s: U256) -> Result<G1Affine> {
    // Converting coordinates to the finite field format
    // and validating that the conversion is successful
    let x1_field = Fq::from_str(x1.to_string().as_str()).ok_or(Error::msg("invalid x1"))?;
    let y1_field = Fq::from_str(y1.to_string().as_str()).ok_or(Error::msg("invalid y1"))?;
    let s_field = Fr::from_str(s.to_string().as_str()).ok_or(Error::msg("invalid s"))?;

    // If one of the points is zero, then both coordinates are zero,
    // which aligns with the from_xy_checked method implementation.
    // However, if some point does not lie on the curve, the method will return an error.
    let point_1 = G1Affine::from_xy_checked(x1_field, y1_field)?;

    let multiplied = point_1.mul(s_field).into_affine();
    Ok(multiplied)
}

pub fn ecmul_function<M: Memory, const B: bool>(
    monotonic_cycle_counter: u32,
    precompile_call_params: LogQuery,
    memory: &mut M,
) -> (
    usize,
    Option<(Vec<MemoryQuery>, Vec<MemoryQuery>, Vec<ECMulRoundWitness>)>,
) {
    let mut processor = ECMulPrecompile::<B>;
    processor.execute_precompile(monotonic_cycle_counter, precompile_call_params, memory)
}

#[cfg(test)]
pub mod tests {
    /// Tests the correctness of the `ecmul_inner` function for a specified point
    /// and a scalar inside the test.
    #[test]
    fn test_ecmul_inner_correctness() {
        use super::*;

        let x1 = U256::from_str_radix(
            "0x1148f79e53544582d22e5071480ae679d0b9df89d69e881f611e8381384ed1ad",
            16,
        )
        .unwrap();
        let y1 = U256::from_str_radix(
            "0xbac10178d2cd8aa9b4af903461b9f1666c219cdfeb2bb5e0cd7cd6486a32a6d",
            16,
        )
        .unwrap();
        let s = U256::from_str_radix(
            "0x15f0e77d431a6c4d21df6a71cdcb0b2eeba21fc1192bd9801b8cd8b7c763e115",
            16,
        )
        .unwrap();

        let result = ecmul_inner((x1, y1), s).unwrap();

        let expected_x = Fq::from_str(
            "9941674825074992183128808489717167636392653540258056893654639521381088261704",
        )
        .unwrap();
        let expected_y = Fq::from_str(
            "8986289197266457569457494475222656986225227492679168701241837087965910154278",
        )
        .unwrap();
        let expected_result = G1Affine::from_xy_checked(expected_x, expected_y).unwrap();

        assert_eq!(result, expected_result);
    }

    /// Tests the correctness of the `ecmul_inner` function for a specified point
    /// taken from https://www.evm.codes/precompiled#0x07
    #[test]
    fn test_ecmul_inner_correctness_evm_codes() {
        use super::*;

        let x1 = U256::from_str_radix("1", 10).unwrap();
        let y1 = U256::from_str_radix("2", 10).unwrap();
        let s = U256::from_str_radix("2", 10).unwrap();

        let result = ecmul_inner((x1, y1), s).unwrap();

        let expected_x = Fq::from_str(
            "1368015179489954701390400359078579693043519447331113978918064868415326638035",
        )
        .unwrap();
        let expected_y = Fq::from_str(
            "9918110051302171585080402603319702774565515993150576347155970296011118125764",
        )
        .unwrap();
        let expected_result = G1Affine::from_xy_checked(expected_x, expected_y).unwrap();

        assert_eq!(result, expected_result);
    }

    /// Tests that the function does not allow to multiply by an invalid point.
    #[test]
    #[should_panic]
    fn test_ecmul_invalid_point() {
        use super::*;

        // (x1, y1) does not lie on the curve
        let x1 = U256::from_str_radix("1", 10).unwrap();
        let y1 = U256::from_str_radix("10", 10).unwrap();
        let s = U256::from_str_radix(
            "0x15f0e77d431a6c4d21df6a71cdcb0b2eeba21fc1192bd9801b8cd8b7c763e115",
            16,
        )
        .unwrap();

        let _ = ecmul_inner((x1, y1), s).unwrap();
    }
}
