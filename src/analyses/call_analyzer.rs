use crate::utils::lifter::IRBlock;
use crate::analyses::reaching_defs::ReachingDefnAnalyzer;
use crate::analyses::AbstractAnalyzer;
use crate::analyses::AnalysisResult;
use crate::utils::ir_utils::{extract_stack_offset, is_stack_access};
use crate::lattices::calllattice::{CallCheckLattice, CallCheckValue, CallCheckValueLattice};
use crate::lattices::davlattice::DAV;
use crate::lattices::reachingdefslattice::{LocIdx, ReachLattice};
use crate::lattices::stacklattice::StackSlot;
use crate::lattices::heaplattice::{WAMR_MODULEINSTANCE_OFFSET, WAMR_FUNCPTRS_OFFSET, WAMR_FUNCTYPE_OFFSET, WAMR_GLOBALS_OFFSET};
use crate::lattices::VarState;
use crate::utils::lifter::{Binopcode, IRMap, MemArg, MemArgs, ValSize, Value};
use crate::utils::utils::{CompilerMetadata, Compiler};
use std::default::Default;

pub struct CallAnalyzer {
    pub metadata: CompilerMetadata,
    pub reaching_defs: AnalysisResult<ReachLattice>,
    pub reaching_analyzer: ReachingDefnAnalyzer,
}

impl AbstractAnalyzer<CallCheckLattice> for CallAnalyzer {

    fn init_state(&self) -> CallCheckLattice {
        let mut result: CallCheckLattice = Default::default();
        if let Compiler::Wamr = self.compiler() {
            result.regs.rdi = CallCheckValueLattice::new(CallCheckValue::WamrExecEnv);
        }
        result
    }

    fn compiler(&self) -> Compiler {
        self.metadata.compiler
    }

    fn analyze_block(
        &self,
        state:  &CallCheckLattice,
        irblock: &IRBlock,
    ) -> CallCheckLattice {
        let mut new_state = state.clone();
        for (addr, instruction) in irblock.iter() {
            for (idx, ir_insn) in instruction.iter().enumerate() {
                self.aexec(
                    &mut new_state,
                    ir_insn,
                    &LocIdx {
                        addr: *addr,
                        idx: idx as u32,
                    },
                );
            }
        }
        new_state
    }

    fn aexec_unop(
        &self,
        in_state: &mut CallCheckLattice,
        dst: &Value,
        src: &Value,
        _loc_idx: &LocIdx,
    ) -> () {
        in_state.set(dst, self.aeval_unop(&in_state, src))
    }

    fn aexec_binop(
        &self,
        in_state: &mut CallCheckLattice,
        opcode: &Binopcode,
        dst: &Value,
        src1: &Value,
        src2: &Value,
        loc_idx: &LocIdx,
    ) -> () {
        match opcode {
            Binopcode::Cmp => {
                match self.compiler() {
                    Compiler::Lucet => self.lucet_handle_cmp(in_state, src1, src2),
                    Compiler::Wamr => self.wamr_handle_cmp(in_state, src1, src2),
                }
            },
            Binopcode::Test => (),
            _ => in_state.set(dst, self.aeval_binop(in_state, opcode, src1, src2, loc_idx)),
        }
    }

    fn process_branch(
        &self,
        irmap: &IRMap,
        in_state: &CallCheckLattice,
        succ_addrs: &Vec<u64>,
        addr: &u64,
    ) -> Vec<(u64, CallCheckLattice)> {
        if succ_addrs.len() == 2 {
            let mut not_branch_state = in_state.clone();
            let mut branch_state = in_state.clone();
            if let Some(CallCheckValue::CheckFlag(val, regnum)) = not_branch_state.regs.zf.v {
                let new_val = CallCheckValueLattice {
                    v: match self.compiler() {
                           Compiler::Lucet => Some(CallCheckValue::CheckedVal),
                           Compiler::Wamr => Some(CallCheckValue::WamrChecked(val)),
                    }
                };
                branch_state.regs.set(
                    &regnum,
                    &ValSize::Size64,
                    new_val.clone(),
                );
                //1. propagate checked values
                let defs_state = self.reaching_defs.get(addr).unwrap();
                let ir_block = irmap.get(addr).unwrap();
                let defs_state = self.reaching_analyzer.analyze_block(defs_state, ir_block);
                let checked_defs = defs_state.regs.get(&regnum, &ValSize::Size64);
                for idx in 0..15 {
                    let reg_def = defs_state.regs.get(&idx, &ValSize::Size64);
                    if (!reg_def.is_empty()) && (reg_def == checked_defs) {
                        branch_state
                            .regs
                            .set(&idx, &ValSize::Size64, new_val.clone());
                    }
                }

                for (stack_offset, stack_slot) in defs_state.stack.map.iter() {
                    if !checked_defs.is_empty() && (stack_slot.value == checked_defs) {
                        let vv = StackSlot {
                            size: stack_slot.size,
                            value: new_val.clone(),
                        };
                        branch_state.stack.map.insert(*stack_offset, vv);
                    }
                }
                
                //3. resolve ptr thunks in registers
                let checked_ptr = CallCheckValueLattice {
                    v: Some(CallCheckValue::PtrOffset(DAV::Checked)),
                };
                for idx in 0..15 {
                    let reg_val = branch_state.regs.get(&idx, &ValSize::Size64);
                    if let Some(CallCheckValue::PtrOffset(DAV::Unchecked(reg_def))) = reg_val.v {
                        if checked_defs.is_empty() && reg_def == checked_defs {
                            branch_state
                                .regs
                                .set(&idx, &ValSize::Size64, checked_ptr.clone());
                        }
                    }
                }

                //4. resolve ptr thunks in stack slots --
                for (stack_offset, stack_slot) in not_branch_state.stack.map.iter() {
                    let stack_val = stack_slot.value.v.clone();
                    if let Some(CallCheckValue::PtrOffset(DAV::Unchecked(stack_def))) = stack_val {
                        if !checked_defs.is_empty() && (stack_def == checked_defs) {
                        let v = StackSlot {
                            size: stack_slot.size,
                            value: checked_ptr.clone(),
                        };
                        branch_state.stack.map.insert(*stack_offset, v);
                        }
                    }
                }
            }
            branch_state.regs.zf = Default::default();
            not_branch_state.regs.zf = Default::default();

            match self.compiler() {
                Compiler::Lucet => return vec![
                    (succ_addrs[0].clone(), not_branch_state),
                    (succ_addrs[1].clone(), branch_state),
                ],
                Compiler::Wamr => return vec![
                    (succ_addrs[0].clone(), branch_state),
                    (succ_addrs[1].clone(), not_branch_state),
                ],
            }
        } else {
            succ_addrs
                .into_iter()
                .map(|addr| (addr.clone(), in_state.clone()))
                .collect()
        }
    }
}

// mem[LucetTableBase + 8]
pub fn is_table_size(in_state: &CallCheckLattice, memargs: &MemArgs) -> bool {
    if let MemArgs::Mem2Args(MemArg::Reg(regnum1, size), MemArg::Imm(_, _, 8)) = memargs {
        if let Some(CallCheckValue::LucetTablesBase) = in_state.regs.get(regnum1, size).v {
            return true;
        }
    }
    false
}

pub fn is_fn_ptr(in_state: &CallCheckLattice, memargs: &MemArgs) -> bool {
    if let MemArgs::Mem3Args(
        MemArg::Reg(regnum1, size1),
        MemArg::Reg(regnum2, size2),
        MemArg::Imm(_, _, immval),
    ) = memargs
    {
        match (
            in_state.regs.get(regnum1, size1).v,
            in_state.regs.get(regnum2, size2).v,
            immval,
        ) {
            (
                Some(CallCheckValue::GuestTableBase),
                Some(CallCheckValue::PtrOffset(DAV::Checked)),
                8,
            ) => return true,
            (
                Some(CallCheckValue::PtrOffset(DAV::Checked)),
                Some(CallCheckValue::GuestTableBase),
                8,
            ) => return true,
            _ => return false,
        }
    }
    false
}

impl CallAnalyzer {
    fn lucet_handle_cmp(&self, in_state: &mut CallCheckLattice, src1: &Value, src2: &Value) {
        match (src1, src2) {
            (Value::Reg(regnum1,size1), Value::Reg(regnum2, size2)) => {
                if let Some(CallCheckValue::TableSize) = in_state.regs.get(regnum2, size2).v{
                    in_state.regs.zf =
                        CallCheckValueLattice::new(CallCheckValue::CheckFlag(0, *regnum1))
                }
                if let Some(CallCheckValue::TableSize) = in_state.regs.get(regnum1, size1).v{
                    in_state.regs.zf =
                        CallCheckValueLattice::new(CallCheckValue::CheckFlag(0, *regnum2))
                }
            }
            _ => (),
        }
    }

    fn wamr_handle_cmp(&self, in_state: &mut CallCheckLattice, src1: &Value, src2: &Value) {
        match (src1, src2) {
            (Value::Imm(_, _, immval), Value::Reg(regnum, regsize)) |
            (Value::Reg(regnum, regsize), Value::Imm(_, _, immval)) => {
                match in_state.regs.get(regnum, regsize).v {
                    Some(_) => (),
                    _ => in_state.regs.zf = CallCheckValueLattice::new(CallCheckValue::CheckFlag(*immval as u32, *regnum)),
                }
            },
            _ => (),
        }
    }

    pub fn aeval_unop(&self, in_state: &CallCheckLattice, value: &Value) -> CallCheckValueLattice {
        match self.compiler() {
            Compiler::Lucet => self.lucet_aeval_unop(in_state, value),
            Compiler::Wamr => self.wamr_aeval_unop(in_state, value),
        }
    }

    fn lucet_aeval_unop(&self, in_state: &CallCheckLattice, value: &Value) -> CallCheckValueLattice {
        match value {
            Value::Mem(memsize, memargs) => {
                if is_table_size(in_state, memargs) {
                    return CallCheckValueLattice {
                        v: Some(CallCheckValue::TableSize),
                    };
                } else if is_fn_ptr(in_state, memargs) {
                    return CallCheckValueLattice {
                        v: Some(CallCheckValue::FnPtr),
                    };
                } else if is_stack_access(value) {
                    let offset = extract_stack_offset(memargs);
                    return in_state.stack.get(offset, memsize.to_u32() / 8);
                }
            }

            Value::Reg(regnum, size) => return in_state.regs.get(regnum, size),

            Value::Imm(_, _, immval) => {
                if (*immval as u64) == self.metadata.guest_table_0 {
                    return CallCheckValueLattice {
                        v: Some(CallCheckValue::GuestTableBase),
                    };
                } else if (*immval as u64) == self.metadata.lucet_tables {
                    return CallCheckValueLattice {
                        v: Some(CallCheckValue::LucetTablesBase),
                    };
                }
            }
        }
        Default::default()
    }

    fn wamr_aeval_unop(&self, in_state: &CallCheckLattice, value: &Value) -> CallCheckValueLattice {
        match value {
            Value::Mem(_memsize, memargs) => {
                match memargs {
                    MemArgs::Mem2Args(MemArg::Reg(regnum, regsize), 
                                      MemArg::Imm(_, _, WAMR_MODULEINSTANCE_OFFSET)) => {

                        if let Some(CallCheckValue::WamrExecEnv) = in_state.regs.get(regnum, regsize).v {
                            return CallCheckValueLattice { v: Some(CallCheckValue::WamrModuleInstance) };
                        }
                    },
                    MemArgs::Mem2Args(MemArg::Reg(regnum, regsize), 
                                      MemArg::Imm(_, _, WAMR_FUNCPTRS_OFFSET)) => {
                        if let Some(CallCheckValue::WamrModuleInstance) = in_state.regs.get(regnum, regsize).v {
                            return CallCheckValueLattice { v: Some(CallCheckValue::WamrFuncPtrsTable) };
                        }
                    },
                    MemArgs::Mem2Args(MemArg::Reg(regnum, regsize), 
                                      MemArg::Imm(_, _, WAMR_FUNCTYPE_OFFSET)) => {
                        if let Some(CallCheckValue::WamrModuleInstance) = in_state.regs.get(regnum, regsize).v {
                            return CallCheckValueLattice { v: Some(CallCheckValue::WamrFuncTypeTable) };
                        }
                    },
                    MemArgs::Mem2Args(MemArg::Reg(base_regnum, ValSize::Size64), MemArg::Imm(_, _, immval)) |
                    MemArgs::MemScaleDisp(MemArg::Reg(base_regnum, ValSize::Size64),
                                          MemArg::Reg(_, ValSize::Size64), MemArg::Imm(_, _, 4),
                                          MemArg::Imm(_, _, immval)) => {
                        // the safety of these accesses is checked in the actual call checker,
                        // the purpose of this code is just to pass on the fact that the result of
                        // this access will be a validated pointer
                        if let Some(CallCheckValue::WamrModuleInstance) = in_state.regs.get(base_regnum, &ValSize::Size64).v {
                            if *immval >= WAMR_GLOBALS_OFFSET-8 {
                                return CallCheckValueLattice { v: Some(CallCheckValue::WamrFuncIdx) };
                            }
                        }
                    }
                    _ => (),
                }
            },
            _ => (),
        }
        Default::default()
    }

    //checked_val << 4
    pub fn aeval_binop(
        &self,
        in_state: &CallCheckLattice,
        opcode: &Binopcode,
        src1: &Value,
        src2: &Value,
        loc_idx: &LocIdx,
    ) -> CallCheckValueLattice {
        if let Binopcode::Shl = opcode {
            if let (Value::Reg(regnum1, size1), Value::Imm(_, _, 4)) = (src1, src2) {
                if let Some(CallCheckValue::CheckedVal) = in_state.regs.get(regnum1, size1).v {
                    return CallCheckValueLattice {
                        v: Some(CallCheckValue::PtrOffset(DAV::Checked)),
                    };
                } else {
                    let def_state = self.reaching_analyzer.fetch_def(&self.reaching_defs, loc_idx);
                    let reg_def = def_state.regs.get(regnum1, size1);
                    return CallCheckValueLattice {
                        v: Some(CallCheckValue::PtrOffset(DAV::Unchecked(reg_def))),
                    };
                }
            }
        }
        Default::default()
    }
}
