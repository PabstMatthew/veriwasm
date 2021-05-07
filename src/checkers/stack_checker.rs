use crate::analyses::stack_analyzer::StackAnalyzer;
use crate::analyses::{AbstractAnalyzer, AnalysisResult};
use crate::checkers::Checker;
use crate::utils::ir_utils::{get_imm_mem_offset, is_stack_access, is_callee_saved_reg};
use crate::lattices::reachingdefslattice::LocIdx;
use crate::lattices::stackgrowthlattice::{StackGrowthLattice, WAMR_STACK_UPPER_BOUND, WAMR_STACK_LOWER_BOUND};
use crate::utils::lifter::{IRMap, MemArgs, Stmt, Value};
use crate::utils::utils::Compiler;
use std::collections::HashMap;

pub struct StackChecker<'a> {
    irmap: &'a IRMap,
    analyzer: &'a StackAnalyzer,
}

pub fn check_stack(
    result: AnalysisResult<StackGrowthLattice>,
    irmap: &IRMap,
    analyzer: &StackAnalyzer,
) -> bool {
    StackChecker {
        irmap: irmap,
        analyzer: analyzer,
    }
    .check(result)
}

/// Checks if it is safe for an operation to clobber a register
fn is_callee_saved_reg_safe(dst: &Value, state: &StackGrowthLattice) -> bool {
    if is_callee_saved_reg(dst) {
        if let Value::Reg(regnum, _regsize) = dst {
            if let Some((_, _, saved)) = &state.v {
                if !saved.contains_key(regnum) {
                    return false;
                }
            } else {
                return false;
            }
        }
    }
    true
}

/// Checks if a stack write will clobber a saved register
fn write_clobbers_callee_saved_reg(offset: i64, saved: &HashMap<u8, i64>) -> bool {
    for saved_offset in saved.values() {
        if *saved_offset == offset {
            return true;
        }
    }
    false
}

impl Checker<StackGrowthLattice> for StackChecker<'_> {
    fn check(&self, result: AnalysisResult<StackGrowthLattice>) -> bool {
        self.check_state_at_statements(result)
    }

    fn irmap(&self) -> &IRMap {
        self.irmap
    }
    fn aexec(&self, state: &mut StackGrowthLattice, ir_stmt: &Stmt, loc: &LocIdx) {
        self.analyzer.aexec(state, ir_stmt, loc)
    }

    fn check_statement(
        &self,
        state: &StackGrowthLattice,
        ir_stmt: &Stmt,
        _loc_idx: &LocIdx,
    ) -> bool {
        //1, stackgrowth is never Bottom or >= 0
        match state.v {
            None => {
                println!("Failure Case: Stackgrowth = None");
                return false;
            }
            Some((stackgrowth, _, _)) => {
                if stackgrowth > 0 {
                    return false;
                }
            }
        }

        // 2. Reads and writes are in bounds
        match ir_stmt {
            //encapsulates both load and store
            Stmt::Unop(_, dst, src) =>
            {
                // make sure that callee-saved registers are not overwritten before being saved
                // (for Wamr only)
                if let Compiler::Wamr = self.analyzer.compiler() { 
                    if !is_callee_saved_reg_safe(dst, state) {
                        println!("modifying a callee-saved register before saving/after restoring!");
                        return false;
                    }
                }

                // stack write: probestack <= stackgrowth + c < 0
                if is_stack_access(dst) {
                    if !self.check_stack_write(state, dst) {
                        println!(
                            "check_stack_write failed: access = {:?} state = {:?}",
                            dst, state
                        );
                        return false;
                    }
                }
                //stack read: probestack <= stackgrowth + c < 8K
                else if is_stack_access(src) {
                    if !self.check_stack_read(state, src) {
                        println!(
                            "check_stack_read failed: access = {:?} state = {:?}",
                            src, state
                        );
                        return false;
                    }
                }
            },
            Stmt::Binop(_, dst, _, _) => {
                // make sure that callee-saved registers are not overwritten before being saved
                // (for Wamr only)
                if let Compiler::Wamr = self.analyzer.compiler() { 
                    if !is_callee_saved_reg_safe(dst, state) {
                        println!("modifying a callee-saved register before saving/after restoring!");
                        return false;
                    }
                }
            },
            _ => (),
        }

        // 3. For all rets stackgrowth = 0
        if let Stmt::Ret = ir_stmt {
            if let Some((stackgrowth, _, _)) = state.v {
                if stackgrowth != 0 {
                    println!("stackgrowth != 0 at ret: stackgrowth = {:?}", stackgrowth);
                    return false;
                }
            }
        }

        true
    }
}

impl StackChecker<'_> {
    fn lucet_check_stack_read(&self, state: &StackGrowthLattice, src: &Value) -> bool {
        if let Value::Mem(_, memargs) = src {
            match memargs {
                MemArgs::Mem1Arg(_memarg) => {
                    return (-state.get_probestack().unwrap() <= state.get_stackgrowth().unwrap())
                        && (state.get_stackgrowth().unwrap() < 8096)
                }
                MemArgs::Mem2Args(_memarg1, memarg2) => {
                    let offset = get_imm_mem_offset(memarg2);
                    return (-state.get_probestack().unwrap()
                        <= state.get_stackgrowth().unwrap() + offset)
                        && (state.get_stackgrowth().unwrap() + offset < 8096);
                }
                _ => return false, //stack accesses should never have 3 args
            }
        }
        panic!("Unreachable")
    }

    fn lucet_check_stack_write(&self, state: &StackGrowthLattice, dst: &Value) -> bool {
        if let Value::Mem(_, memargs) = dst {
            match memargs {
                MemArgs::Mem1Arg(_memarg) => {
                    return (-state.get_probestack().unwrap() <= state.get_stackgrowth().unwrap())
                        && (state.get_stackgrowth().unwrap() < 0);
                }
                MemArgs::Mem2Args(_memarg1, memarg2) => {
                    let offset = get_imm_mem_offset(memarg2);
                    return (-state.get_probestack().unwrap()
                        <= state.get_stackgrowth().unwrap() + offset)
                        && (state.get_stackgrowth().unwrap() + offset < 0);
                }
                _ => return false, //stack accesses should never have 3 args
            }
        }
        panic!("Unreachable")
    }

    fn wamr_check_stack_read(&self, state: &StackGrowthLattice, src: &Value) -> bool {
        if let Value::Mem(_, memargs) = src {
            if let Some((stackgrowth, _, _)) = &state.v {
                match memargs {
                    MemArgs::Mem1Arg(_memarg) => {
                        return *stackgrowth < WAMR_STACK_UPPER_BOUND &&
                               *stackgrowth > WAMR_STACK_LOWER_BOUND;
                    },
                    MemArgs::Mem2Args(_memarg1, memarg2) => {
                        let offset = stackgrowth + get_imm_mem_offset(memarg2);
                        return offset < WAMR_STACK_UPPER_BOUND &&
                               offset > WAMR_STACK_LOWER_BOUND;
                    },
                    _ => return false, //stack accesses should never have 3 args
                }
            }
        }
        panic!("Unreachable")
    }

    fn wamr_check_stack_write(&self, state: &StackGrowthLattice, dst: &Value) -> bool {
        if let Value::Mem(_, memargs) = dst {
            if let Some((stackgrowth, _, saved)) = &state.v {
                match memargs {
                    MemArgs::Mem1Arg(_memarg) => {
                        if write_clobbers_callee_saved_reg(*stackgrowth, saved) {
                            return false;
                        }
                        return *stackgrowth < 0 &&
                               *stackgrowth > WAMR_STACK_LOWER_BOUND;
                    },
                    MemArgs::Mem2Args(_memarg1, memarg2) => {
                        let offset = *stackgrowth + get_imm_mem_offset(memarg2);
                        if write_clobbers_callee_saved_reg(offset, saved) {
                            return false;
                        }
                        return offset < 0 &&
                               offset > WAMR_STACK_LOWER_BOUND;
                    },
                    _ => return false, //stack accesses should never have 3 args
                }
            }
        }
        panic!("Unreachable")
    }

    fn check_stack_read(&self, state: &StackGrowthLattice, src: &Value) -> bool {
        match self.analyzer.compiler() {
            Compiler::Lucet => self.lucet_check_stack_read(state, src),
            Compiler::Wamr => self.wamr_check_stack_read(state, src),
        }
    }

    fn check_stack_write(&self, state: &StackGrowthLattice, src: &Value) -> bool {
        match self.analyzer.compiler() {
            Compiler::Lucet => self.lucet_check_stack_write(state, src),
            Compiler::Wamr => self.wamr_check_stack_write(state, src),
        }
    }
}
