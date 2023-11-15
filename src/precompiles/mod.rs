use crate::aux::*;
use crate::queries::*;
use crate::vm::*;

pub mod ecrecover;
pub mod keccak256;
pub mod secp256r1_verify;
pub mod sha256;

use zkevm_opcode_defs::system_params::{
    ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS, KECCAK256_ROUND_FUNCTION_PRECOMPILE_ADDRESS,
    SECP256R1_VERIFY_PRECOMPILE_ADDRESS, SHA256_ROUND_FUNCTION_PRECOMPILE_ADDRESS,
};

use zkevm_opcode_defs::PrecompileCallABI;

pub const fn precompile_abi_in_log(query: LogQuery) -> PrecompileCallABI {
    PrecompileCallABI::from_u256(query.key)
}

#[derive(Clone, Copy, Debug)]
pub struct DefaultPrecompilesProcessor<const B: bool>;

impl<const B: bool> PrecompilesProcessor for DefaultPrecompilesProcessor<B> {
    fn start_frame(&mut self) {
        // there are no precompiles to rollback, do nothing
    }
    fn execute_precompile<M: Memory>(
        &mut self,
        monotonic_cycle_counter: u32,
        query: LogQuery,
        memory: &mut M,
    ) -> Option<(Vec<MemoryQuery>, Vec<MemoryQuery>, PrecompileCyclesWitness)> {
        let address_low = u16::from_le_bytes([query.address.0[19], query.address.0[18]]);
        match address_low {
            KECCAK256_ROUND_FUNCTION_PRECOMPILE_ADDRESS => {
                // pure function call, non-revertable
                if B {
                    let (reads, writes, round_witness) =
                        keccak256::keccak256_rounds_function::<M, B>(
                            monotonic_cycle_counter,
                            query,
                            memory,
                        )
                        .expect("must generate intermediate witness");

                    Some((
                        reads,
                        writes,
                        PrecompileCyclesWitness::Keccak256(round_witness),
                    ))
                } else {
                    let _ = keccak256::keccak256_rounds_function::<M, B>(
                        monotonic_cycle_counter,
                        query,
                        memory,
                    );

                    None
                }
            }
            SHA256_ROUND_FUNCTION_PRECOMPILE_ADDRESS => {
                // pure function call, non-revertable
                if B {
                    let (reads, writes, round_witness) = sha256::sha256_rounds_function::<M, B>(
                        monotonic_cycle_counter,
                        query,
                        memory,
                    )
                    .expect("must generate intermediate witness");

                    Some((
                        reads,
                        writes,
                        PrecompileCyclesWitness::Sha256(round_witness),
                    ))
                } else {
                    let _ = sha256::sha256_rounds_function::<M, B>(
                        monotonic_cycle_counter,
                        query,
                        memory,
                    );

                    None
                }
            }
            ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS => {
                // pure function call, non-revertable
                if B {
                    let (reads, writes, round_witness) = ecrecover::ecrecover_function::<M, B>(
                        monotonic_cycle_counter,
                        query,
                        memory,
                    )
                    .expect("must generate intermediate witness");

                    Some((
                        reads,
                        writes,
                        PrecompileCyclesWitness::ECRecover(round_witness),
                    ))
                } else {
                    let _ = ecrecover::ecrecover_function::<M, B>(
                        monotonic_cycle_counter,
                        query,
                        memory,
                    );

                    None
                }
            }
            SECP256R1_VERIFY_PRECOMPILE_ADDRESS => {
                if B {
                    let (reads, writes, round_witness) =
                        secp256r1_verify::secp256r1_verify_function::<M, B>(
                            monotonic_cycle_counter,
                            query,
                            memory,
                        )
                        .expect("must generate intermediate witness");

                    Some((
                        reads,
                        writes,
                        PrecompileCyclesWitness::Secp256r1Verify(round_witness),
                    ))
                } else {
                    let _ = secp256r1_verify::secp256r1_verify_function::<M, B>(
                        monotonic_cycle_counter,
                        query,
                        memory,
                    );

                    None
                }
            }
            _ => {
                // it's formally allowed for purposes of ergs-burning
                // by system contracts

                None
            }
        }
    }

    fn finish_frame(&mut self, _panicked: bool) {
        // there are no revertable precompile yes, so we are ok
    }
}
