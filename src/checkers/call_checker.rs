use crate::analyses::call_analyzer::CallAnalyzer;
use crate::analyses::{AbstractAnalyzer, AnalysisResult};
use crate::checkers::Checker;
use crate::lattices::calllattice::{CallCheckLattice, CallCheckValue};
use crate::lattices::davlattice::DAV;
use crate::lattices::reachingdefslattice::LocIdx;
use crate::lattices::heaplattice::WAMR_GLOBALS_OFFSET;
use crate::utils::lifter::{IRMap, MemArg, MemArgs, Stmt, ValSize, Value};
use crate::utils::utils::Compiler;

pub struct CallChecker<'a> {
    irmap: &'a IRMap,
    analyzer: &'a CallAnalyzer,
    funcs: &'a Vec<u64>,
    plt: &'a (u64,u64),
    // x86_64_data: &x86_64Data,
}

pub fn check_calls(
    result: AnalysisResult<CallCheckLattice>,
    irmap: &IRMap,
    analyzer: &CallAnalyzer,
    funcs: &Vec<u64>,
    plt: &(u64,u64),
    // x86_64_data: &x86_64Data,
) -> bool {
    CallChecker {
        irmap,
        analyzer,
        funcs,
        plt
        // x86_64_data,
    }
    .check(result)
}

impl Checker<CallCheckLattice> for CallChecker<'_> {
    fn check(&self, result: AnalysisResult<CallCheckLattice>) -> bool {
        self.check_state_at_statements(result)
    }

    fn irmap(&self) -> &IRMap {
        self.irmap
    }
    fn aexec(&self, state: &mut CallCheckLattice, ir_stmt: &Stmt, loc: &LocIdx) {
        self.analyzer.aexec(state, ir_stmt, loc)
    }

    fn check_statement(&self, state: &CallCheckLattice, ir_stmt: &Stmt, loc_idx: &LocIdx) -> bool {
        //1. Check that all indirect calls use resolved function pointer
        if let Stmt::Call(v) = ir_stmt {
            if !self.check_indirect_call(state, v, loc_idx) {
                println!("0x{:x} Failure Case: Indirect Call {:?}", loc_idx.addr, v);
                return false;
            }
        }

        // 2. Check that lookup is using resolved DAV
        if let Stmt::Unop(_, _, Value::Mem(_, memargs)) = ir_stmt {
            if !self.check_calltable_lookup(state, memargs) {
                println!("0x{:x} Failure Case: Lookup Call: {:?}", loc_idx.addr, memargs);
                print_mem_access(state, memargs);
                return false;
            }
        }
        true
    }
}

impl CallChecker<'_> {
    fn check_indirect_call(
        &self,
        state: &CallCheckLattice,
        target: &Value,
        loc_idx: &LocIdx,
    ) -> bool {
        match self.analyzer.compiler() {
            Compiler::Lucet => self.lucet_check_indirect_call(state, target, loc_idx),
            Compiler::Wamr => self.wamr_check_indirect_call(state, target, loc_idx),
        }
    }

    fn lucet_check_indirect_call(
        &self,
        state: &CallCheckLattice,
        target: &Value,
        loc_idx: &LocIdx,
    ) -> bool {
        match target {
            Value::Reg(regnum, size) => {
                if let Some(CallCheckValue::FnPtr) = state.regs.get(regnum, size).v {
                    return true;
                }
                else{
                    println!("{:?}", state.regs.get(regnum, size).v)
                }
            }
            Value::Mem(_, _) => return false,
            Value::Imm(_, _, imm) => {
                let target = (*imm + (loc_idx.addr as i64) + 5) as u64;
                let (plt_start, plt_end) = self.plt;
                return self.funcs.contains(&target) || 
                ((target >= *plt_start) && (target < *plt_end)) ; 
            }, 
        }
        false
    }

    fn wamr_check_indirect_call(
        &self,
        state: &CallCheckLattice,
        target: &Value,
        loc_idx: &LocIdx,
    ) -> bool {
        match target {
            Value::Mem(_, memargs) => {
                match memargs {
                    // check that indirect call lookups use a valid base and index
                    // (this must match Case 3 in check_jump_table_access in the heap checker)
                    MemArgs::MemScale(MemArg::Reg(base_regnum, base_regsize),
                                      MemArg::Reg(idx_regnum, ValSize::Size64), MemArg::Imm(_, _, 8)) => {
                        if let Some(CallCheckValue::WamrFuncPtrsTable) = state.regs.get(base_regnum, base_regsize).v {
                            if let Some(CallCheckValue::WamrFuncIdx) = state.regs.get(idx_regnum, &ValSize::Size64).v {
                                return true;
                            } else {
                                println!("indirect call without valid function index: {:?}", 
                                         state.regs.get(idx_regnum, &ValSize::Size64).v);
                                return false;
                            }
                        } else {
                            println!("indirect call without valid base address: {:?}", memargs);
                            return false;
                        }
                    },
                    _ => (),
                }
            },
            Value::Imm(_, _, imm) => {
                let target = (*imm + (loc_idx.addr as i64) + 5) as u64;
                return self.funcs.contains(&target);
            }, 
            _ => (),
        }
        false
    }

    fn check_calltable_lookup(&self, state: &CallCheckLattice, memargs: &MemArgs) -> bool {
        match self.analyzer.compiler() {
            Compiler::Lucet => self.lucet_check_calltable_lookup(state, memargs),
            Compiler::Wamr => self.wamr_check_calltable_lookup(state, memargs),
        }
    }

    fn lucet_check_calltable_lookup(&self, state: &CallCheckLattice, memargs: &MemArgs) -> bool {
        // println!("Call Table Lookup: {:?}", memargs);
        match memargs {
            MemArgs::Mem3Args(
                MemArg::Reg(regnum1, ValSize::Size64),
                MemArg::Reg(regnum2, ValSize::Size64),
                MemArg::Imm(_, _, 8),
            ) => match (
                state.regs.get(regnum1, &ValSize::Size64).v,
                state.regs.get(regnum2, &ValSize::Size64).v,
            ) {
                (
                    Some(CallCheckValue::GuestTableBase),
                    Some(CallCheckValue::PtrOffset(DAV::Checked)),
                ) => return true,
                (
                    Some(CallCheckValue::PtrOffset(DAV::Checked)),
                    Some(CallCheckValue::GuestTableBase),
                ) => return true,
                (_x, Some(CallCheckValue::GuestTableBase))
                | (Some(CallCheckValue::GuestTableBase), _x) => return false,
                (_x, _y) => return true, // not a calltable lookup
            },
            _ => return true, //not a calltable lookup?
        }
    }

    fn wamr_check_calltable_lookup(&self, state: &CallCheckLattice, memargs: &MemArgs) -> bool {
        let lower_bound = WAMR_GLOBALS_OFFSET;
        let upper_bound = lower_bound + self.analyzer.metadata.globals_size;
        match memargs {
            // the cases here must match Case 1 for check_jump_table_access in the heap checker
            MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), MemArg::Imm(_, _, immval)) => {
                if let Some(CallCheckValue::WamrModuleInstance) = state.regs.get(regnum, &ValSize::Size64).v {
                    if *immval >= lower_bound {
                        return *immval >= lower_bound && *immval <= upper_bound;
                    }
                }
            },
            MemArgs::MemScaleDisp(MemArg::Reg(base_regnum, ValSize::Size64),
                                  MemArg::Reg(idx_regnum, ValSize::Size64), MemArg::Imm(_, _, 4),
                                  MemArg::Imm(_, _, WAMR_GLOBALS_OFFSET)) => {
                if let Some(CallCheckValue::WamrModuleInstance) = state.regs.get(base_regnum, &ValSize::Size64).v {
                    if let Some(CallCheckValue::WamrChecked(val)) = state.regs.get(idx_regnum, &ValSize::Size64).v {
                        return val < (self.analyzer.metadata.globals_size as u32);
                    } else {
                        println!("unchecked index into the function index table!");
                        return false;
                    }
                }
            },
            // check that function type table lookups use a valid index 
            // (must match Case 2 for check_jump_table_access in the heap checker)
            MemArgs::MemScale(MemArg::Reg(regnum, ValSize::Size64),
                              MemArg::Reg(_, ValSize::Size64), MemArg::Imm(_, _, 4)) => {
                if let Some(CallCheckValue::WamrFuncTypeTable) = state.regs.get(regnum, &ValSize::Size64).v {
                    return true;
                } else {
                    println!("function type table lookup without valid index!");
                    return false;
                }
            }
            _ => (),
        }
        true // not a recognized function index lookup
    }
}

pub fn memarg_repr(state: &CallCheckLattice, memarg: &MemArg) -> String {
    match memarg {
        MemArg::Reg(regnum, size) => format!("r{:?}: {:?}", regnum, state.regs.get(regnum, size).v),
        MemArg::Imm(_, _, x) => format!("{:?}", x),
    }
}

pub fn print_mem_access(state: &CallCheckLattice, memargs: &MemArgs) {
    match memargs {
        MemArgs::Mem1Arg(x) => println!("mem[{:?}]", memarg_repr(state, x)),
        MemArgs::Mem2Args(x, y) => println!(
            "mem[{:?} + {:?}]",
            memarg_repr(state, x),
            memarg_repr(state, y)
        ),
        MemArgs::Mem3Args(x, y, z) => println!(
            "mem[{:?} + {:?} + {:?}]",
            memarg_repr(state, x),
            memarg_repr(state, y),
            memarg_repr(state, z)
        ),
        MemArgs::MemScale(x, y, z) => println!(
            "mem[{:?} + {:?} * {:?}]",
            memarg_repr(state, x),
            memarg_repr(state, y),
            memarg_repr(state, z)
        ),
        MemArgs::MemScaleDisp(w, x, y, z) => println!(
            "mem[{:?} + {:?}*{:?} + {:?}]",
            memarg_repr(state, w),
            memarg_repr(state, x),
            memarg_repr(state, y),
            memarg_repr(state, z)
        ),
    }
}
