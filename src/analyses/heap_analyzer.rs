use crate::analyses::AbstractAnalyzer;
use crate::utils::ir_utils::{extract_stack_offset, is_stack_access};
use crate::lattices::heaplattice::{HeapLattice, HeapValue, HeapValueLattice};
use crate::lattices::heaplattice::{WAMR_MODULEINSTANCE_OFFSET, WAMR_HEAPBASE_OFFSET};
use crate::lattices::reachingdefslattice::LocIdx;
use crate::lattices::VarState;
use crate::utils::lifter::{MemArg, MemArgs, ValSize, Value};
use crate::utils::utils::{CompilerMetadata, Compiler};
use std::default::Default;

pub struct HeapAnalyzer {
    pub metadata: CompilerMetadata,
}

impl AbstractAnalyzer<HeapLattice> for HeapAnalyzer {
    fn init_state(&self) -> HeapLattice {
        let mut result: HeapLattice = Default::default();
        match self.metadata.compiler {
            Compiler::Lucet => result.regs.rdi = HeapValueLattice::new(HeapValue::HeapBase),
            Compiler::Wamr => result.regs.rdi = HeapValueLattice::new(HeapValue::WamrExecEnv),
        }
        result
    }

    fn compiler(&self) -> Compiler {
        self.metadata.compiler
    }

    fn aexec_unop(
        &self,
        in_state: &mut HeapLattice,
        dst: &Value,
        src: &Value,
        _loc_idx: &LocIdx,
    ) -> () {
        let mut v: HeapValueLattice = self.aeval_unop(in_state, src);
        if v == HeapValueLattice::default() {
            if let Value::Reg(_, ValSize::Size32) = dst {
                // in x86, mov'ing to a 32b register clears the upper 32b of the corresponding
                // 64b register. We need to communicate this state to enable checking of future
                // accesses that use the 64b register (for Wamr).
                v = HeapValueLattice::new(HeapValue::Bounded4GB);
            }
        }
        in_state.set(dst, v)
    }
}

pub fn lucet_is_globalbase_access(in_state: &HeapLattice, memargs: &MemArgs) -> bool {
    if let MemArgs::Mem2Args(arg1, _arg2) = memargs {
        if let MemArg::Reg(regnum, size) = arg1 {
            assert_eq!(size.to_u32(), 64);
            let base = in_state.regs.get(regnum, size);
            if let Some(v) = base.v {
                if let HeapValue::HeapBase = v {
                    return true;
                }
            }
        }
    };
    false
}

/*
 * Helper function to check for accesses of the form mem[base_val + offset]
 */
fn wamr_access_helper(in_state: &HeapLattice, memargs: &MemArgs, base_val: HeapValue, offset: i64) -> bool {
    if let MemArgs::Mem2Args(arg1, arg2) = memargs {
        if let MemArg::Reg(regnum, regsize) = arg1 {
            if regsize.to_u32() == 64 {
                let base = in_state.regs.get(regnum, regsize);
                if let Some(v) = base.v {
                    if v == base_val {
                        if let MemArg::Imm(_, _, immval) = arg2 {
                            if *immval == offset {
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

/*
 * Checks if a memory access is to Wamr's AOTModuleInstance pointer within the current ExecEnv.
 *  The access must be of the form mem[WamrExecEnv + WAMR_MODULEINSTANCE_OFFSET] 
 *  (see lattices/heaplattice.rs for more details)
 */
pub fn wamr_is_moduleinstance_access(in_state: &HeapLattice, memargs: &MemArgs) -> bool {
    return wamr_access_helper(in_state, memargs, 
                       HeapValue::WamrExecEnv, 
                       WAMR_MODULEINSTANCE_OFFSET);
}

/*
 * Checks if a memory access is to Wamr's heap base pointer within the current AOTModuleInstance.
 *  The access must be of the form mem[WamrModuleInstance + WAMR_HEAPBASE_OFFSET] 
 *  (see lattices/heaplattice.rs for more details)
 */
pub fn wamr_is_heapbase_access(in_state: &HeapLattice, memargs: &MemArgs) -> bool {
    return wamr_access_helper(in_state, memargs, 
                       HeapValue::WamrModuleInstance, 
                       WAMR_HEAPBASE_OFFSET);
}

impl HeapAnalyzer {
    pub fn aeval_unop(&self, in_state: &mut HeapLattice, value: &Value) -> HeapValueLattice {
        match self.metadata.compiler {
            Compiler::Lucet => self.lucet_aeval_unop(in_state, value),
            Compiler::Wamr => self.wamr_aeval_unop(in_state, value),
        }
    }

    fn wamr_aeval_unop(&self, in_state: &mut HeapLattice, value: &Value) -> HeapValueLattice {
        match value {
            Value::Mem(_memsize, memargs) => {
                if wamr_is_moduleinstance_access(in_state, memargs) {
                    return HeapValueLattice::new(HeapValue::WamrModuleInstance);
                }
                if wamr_is_heapbase_access(in_state, memargs) {
                    return HeapValueLattice::new(HeapValue::HeapBase);
                }
            },
            Value::Reg(regnum, size) => {
                if let ValSize::SizeOther = size {
                    return Default::default();
                };
                if size.to_u32() <= 32 {
                    return HeapValueLattice::new(HeapValue::Bounded4GB);
                } else {
                    return in_state.regs.get(regnum, &ValSize::Size64);
                }
            },
            Value::Imm(_, _, _immval) => {},
        }
        Default::default()
    }

    fn lucet_aeval_unop(&self, in_state: &mut HeapLattice, value: &Value) -> HeapValueLattice {
        match value {
            Value::Mem(memsize, memargs) => {
                if lucet_is_globalbase_access(in_state, memargs) {
                    return HeapValueLattice::new(HeapValue::GlobalsBase);
                }
                if is_stack_access(value) {
                    let offset = extract_stack_offset(memargs);
                    let v = in_state.stack.get(offset, memsize.to_u32() / 8);
                    return v;
                }
            }

            Value::Reg(regnum, size) => {
                if let ValSize::SizeOther = size {
                    return Default::default();
                };
                if size.to_u32() <= 32 {
                    return HeapValueLattice::new(HeapValue::Bounded4GB);
                } else {
                    return in_state.regs.get(regnum, &ValSize::Size64);
                }
            }

            Value::Imm(_, _, immval) => {
                if (*immval as u64) == self.metadata.guest_table_0 {
                    return HeapValueLattice::new(HeapValue::GuestTable0);
                } else if (*immval as u64) == self.metadata.lucet_tables {
                    return HeapValueLattice::new(HeapValue::LucetTables);
                } else if (*immval >= 0) && (*immval < (1 << 32)) {
                    return HeapValueLattice::new(HeapValue::Bounded4GB);
                }
            }
        }
        Default::default()
    }
}
