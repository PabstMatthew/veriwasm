use crate::analyses::AbstractAnalyzer;
use crate::utils::ir_utils::{get_imm_offset, is_rsp, is_callee_saved_reg, memarg_is_stack};
use crate::lattices::reachingdefslattice::LocIdx;
use crate::lattices::stackgrowthlattice::StackGrowthLattice;
use crate::utils::lifter::{Unopcode, Binopcode, Stmt, Value, MemArgs};
use crate::utils::utils::{CompilerMetadata, Compiler};
use std::collections::HashMap;

pub struct StackAnalyzer {
    pub metadata: CompilerMetadata,
}

impl AbstractAnalyzer<StackGrowthLattice> for StackAnalyzer {
    fn init_state(&self) -> StackGrowthLattice {
        StackGrowthLattice::new((0, 4096, HashMap::new()))
    }

    fn compiler(&self) -> Compiler {
        self.metadata.compiler
    }

    fn aexec(&self, in_state: &mut StackGrowthLattice, ir_instr: &Stmt, loc_idx: &LocIdx) -> () {
        match self.compiler() {
            Compiler::Lucet => self.lucet_aexec(in_state, ir_instr, loc_idx),
            Compiler::Wamr => self.wamr_aexec(in_state, ir_instr, loc_idx),
        }
    }
}

impl StackAnalyzer {
    fn lucet_aexec(&self, in_state: &mut StackGrowthLattice, ir_instr: &Stmt, _loc_idx: &LocIdx) -> () {
        match ir_instr {
            Stmt::Clear(dst, _) => {
                if is_rsp(dst) {
                    in_state.clear();
                }
            }
            Stmt::Unop(_, dst, _) => {
                if is_rsp(dst) {
                    in_state.clear();
                }
            }
            Stmt::Binop(Binopcode::Cmp, _, _, _) => (),
            Stmt::Binop(Binopcode::Test, _, _, _) => (),
            Stmt::Binop(opcode, dst, src1, src2) => {
                if is_rsp(dst) {
                    if is_rsp(src1) {
                        let offset = get_imm_offset(src2);
                        if let Some((x, probestack, _)) = &mut in_state.v {
                            match opcode {
                                Binopcode::Add => {
                                    *x += offset;
                                }
                                Binopcode::Sub => {
                                    if (offset - *x) > *probestack + 4096 {
                                        panic!("Probestack, _ violation")
                                    } else if (offset - *x) > *probestack {
                                        //if we touch next page after the space
                                        //we've probed, it cannot skip guard page
                                        *x -= offset;
                                        *probestack += 4096;
                                        return;
                                    }
                                    *x -= offset;
                                }
                                _ => panic!("Illegal RSP write"),
                            }
                        } else {
                            in_state.clear();
                        }
                    } else {
                        in_state.clear();
                    }
                }
            }
            Stmt::ProbeStack(new_probestack) => {
                if let Some((x, probestack, _)) = &mut in_state.v {
                    let probed = (((*new_probestack / 4096) + 1) * 4096) as i64; // Assumes page size of 4096
                    *x -= *new_probestack as i64;
                    *probestack = probed;
                } else {
                    in_state.clear();
                }
            }
            _ => (),
        }
    }

    fn wamr_aexec(&self, in_state: &mut StackGrowthLattice, ir_instr: &Stmt, _loc_idx: &LocIdx) -> () {
        match ir_instr {
            Stmt::Clear(dst, _) => {
                // clearing RSP should invalidate all our analysis
                if is_rsp(dst) {
                    in_state.clear();
                }
            },
            Stmt::Unop(opcode, dst, src) => self.wamr_handle_unop(in_state, opcode, dst, src),
            Stmt::Binop(opcode, dst, src1, src2) => self.wamr_handle_binop(in_state, opcode, dst, src1, src2),
            _ => (),
        }
    }

    fn wamr_handle_unop(&self, in_state: &mut StackGrowthLattice, 
                         _opcode: &Unopcode, dst: &Value, src: &Value) -> () {
        // arbitrarily modifying RSP should invalidate all our analysis
        if is_rsp(dst) {
            in_state.clear();
        } 

        // if a callee-saved register is being stored to a stack offset, keep track of it
        // internally to ensure it's not modified during the function, and is restored properly.
        if is_callee_saved_reg(src) {
            if let Value::Reg(regnum, regsize) = src {
                if let Value::Mem(_memsize, memargs) = dst {
                    if let MemArgs::Mem1Arg(memarg) = memargs {
                        if memarg_is_stack(memarg) {
                            assert!(regsize.to_u32() == 64);
                            if let Some((stack_growth, _probestack, saved)) = &mut in_state.v {
                                // pushing a callee-saved register
                                assert!(*stack_growth <= 0, 
                                        "stack growth should be within the current stack frame!");
                                assert!(!saved.contains_key(regnum), 
                                        "pushed the same register twice!");
                                saved.insert(*regnum, *stack_growth);
                            } else {
                                panic!("pushing callee-saved register without any known stack state!");
                            }
                        }
                    }
                }
            }
        }
        // if a callee-saved register is being restored from the stack, let's make sure that the
        // stack offset matches the offset when it was pushed.
        if is_callee_saved_reg(dst) {
            if let Value::Reg(regnum, regsize) = dst {
                if let Value::Mem(_memsize, memargs) = src {
                    if let MemArgs::Mem1Arg(memarg) = memargs {
                        if memarg_is_stack(memarg) {
                            assert!(regsize.to_u32() == 64);
                            if let Some((stack_growth, _probestack, saved)) = &mut in_state.v {
                                // popping a callee-saved register
                                assert!(saved.contains_key(regnum), 
                                        "popping register that was never pushed!");
                                assert!(*saved.get(regnum).unwrap() == *stack_growth, 
                                        "mismatched push/pop for callee-saved register!");
                                saved.remove(regnum);
                            } else {
                                panic!("pushing callee-saved register without any known stack state!");
                            }
                        }
                    }
                }
            }
        }
        // It's possible that the analysis above is not precise (it may accidentally identify
        // normal loads/stores as pushes/pops), but it is still sound in that pushes/pops or
        // malicious loads/stores cannot escape detection.
    }

    fn wamr_handle_binop(&self, in_state: &mut StackGrowthLattice, 
                         opcode: &Binopcode, dst: &Value, src1: &Value, src2: &Value) -> () {
        // handle RSP modifications
        if is_rsp(dst) {
            if is_rsp(src1) {
                let offset = get_imm_offset(src2);
                if let Some((x, probestack, _saved)) = &mut in_state.v {
                    match opcode {
                        Binopcode::Add => {
                            *x += offset;
                        }
                        Binopcode::Sub => {
                            if (offset - *x) > *probestack + 4096 {
                                panic!("Probestack, _ violation")
                            } else if (offset - *x) > *probestack {
                                //if we touch next page after the space
                                //we've probed, it cannot skip guard page
                                *x -= offset;
                                *probestack += 4096;
                                return;
                            }
                            *x -= offset;
                        }
                        _ => panic!("Illegal RSP write"),
                    }
                } else {
                    in_state.clear();
                }
            }
        }
    }
}
