use crate::lattices::stacklattice::StackSlot;
use crate::lattices::reachingdefslattice::{ReachingDefnLattice, LocIdx,ReachLattice};
use crate::analyses::reaching_defs::ReachingDefnAnalyzer;
use crate::analyses::analyze_block;
use crate::ir_utils::{extract_stack_offset, is_stack_access};
use crate::lattices::calllattice::{CallCheckLattice, CallCheckValue, CallCheckValueLattice};
use crate::lattices::davlattice::DAV;
use crate::lifter::{MemArgs, MemArg, Binopcode, IRMap, Value, ValSize};
use crate::analyses::AnalysisResult;
use crate::analyses::{AbstractAnalyzer};
use crate::utils::{LucetMetadata};
use std::default::Default;
use crate::lattices::VarState;
use std::collections::BTreeSet;

pub struct CallAnalyzer{
    pub metadata: LucetMetadata,
    pub reaching_defs : AnalysisResult<ReachLattice>,
    pub reaching_analyzer : ReachingDefnAnalyzer
}

impl AbstractAnalyzer<CallCheckLattice> for CallAnalyzer {
    fn aexec_unop(&self, in_state : &mut CallCheckLattice, dst : &Value, src : &Value) -> (){
        in_state.set(dst, self.aeval_unop(in_state, src))
    }

    fn aexec_binop(&self, in_state : &mut CallCheckLattice, opcode : &Binopcode, dst: &Value, src1 : &Value, src2: &Value) -> (){
        in_state.set(dst, self.aeval_binop(in_state, opcode, src1, src2))
    }

    //TODO: need to add final instruction to process_branch args
    //TODO: figure out how to extract zflag
    fn process_branch(&self, irmap : &IRMap, in_state : &CallCheckLattice, succ_addrs : &Vec<u64>, addr : &u64) -> Vec<(u64,CallCheckLattice)>{
        if succ_addrs.len() == 2{
            let mut not_branch_state = in_state.clone();
            let mut branch_state = in_state.clone();
            //if zf = CheckFlag(regnum) and and state.get(regnum) == PtrOffset
            //=> state.set(regnum, PtrOffset(Checked)) 
            //TODO: set zf to checkflag
            // if let Some(SwitchValue::ZF(bound, regnum)) = not_branch_state.regs.zf.v{
            //     not_branch_state.regs.set(&regnum, SwitchValueLattice{v: Some(SwitchValue::UpperBound(bound))})
            // }

            //1. propagate checked values
            let defs_state = self.reaching_defs.get(addr).unwrap();
            let ir_block = irmap.get(addr).unwrap();
            let defs_state = analyze_block(&self.reaching_analyzer, defs_state, ir_block);
            let checked_defs = defs_state.regs.zf.clone();
            let new_val = CallCheckValueLattice{ v : Some(CallCheckValue::CheckedVal)};
            for idx in 0..15{
                let reg_def = defs_state.regs.get(&idx, &ValSize::Size64);
                if (!reg_def.is_empty()) && (reg_def == checked_defs){
                    branch_state.regs.set(&idx, &ValSize::Size64, new_val.clone()); 
                }
            }
            //2. resolve ptr thunks in registers
            let checked_ptr = CallCheckValueLattice{ v : Some(CallCheckValue::PtrOffset(DAV::Checked))};
            for idx in 0..15{
                let reg_val = branch_state.regs.get(&idx, &ValSize::Size64);
                if let Some(CallCheckValue::PtrOffset(DAV::Unchecked(reg_def))) = reg_val.v{
                    if reg_def == checked_defs{
                        branch_state.regs.set(&idx, &ValSize::Size64, checked_ptr.clone());
                    }
                }
            }
            
            //3. resolve ptr thunks in stack slots -- TODO
            for (stack_offset, stack_slot) in defs_state.stack.map.iter(){
                if !checked_defs.is_empty() && (stack_slot.value == checked_defs){
                    let v = StackSlot{size: stack_slot.size, value : checked_ptr.clone()};
                    branch_state.stack.map.insert(*stack_offset, v);
                }
            }

            vec![(succ_addrs[0].clone(),not_branch_state), (succ_addrs[1].clone(),branch_state)]
            //succ_addrs.into_iter().map(|addr| (addr.clone(),in_state.clone()) ).collect()
        }
        else {succ_addrs.into_iter().map(|addr| (addr.clone(),in_state.clone()) ).collect()}
    }
}

// mem[LucetTableBase + 8]
pub fn is_table_size(in_state : &CallCheckLattice, memargs : &MemArgs) -> bool{
    if let MemArgs::Mem2Args(MemArg::Reg(regnum1,size), MemArg::Imm(_,_,8)) = memargs{ 
        if let Some(CallCheckValue::LucetTablesBase) = in_state.regs.get(regnum1, size).v{
            return true 
        }
    }
    false
}


pub fn is_fn_ptr(in_state : &CallCheckLattice, memargs : &MemArgs) -> bool{
    if let MemArgs::Mem3Args(MemArg::Reg(regnum1,size1), MemArg::Reg(regnum2,size2), MemArg::Imm(_,_,immval))  = memargs{ 
        {
        match (in_state.regs.get(regnum1, size1).v,in_state.regs.get(regnum2, size2).v,immval){
            (Some(CallCheckValue::GuestTableBase),Some(CallCheckValue::PtrOffset(DAV::Checked)),8) => return true,
            (Some(CallCheckValue::PtrOffset(DAV::Checked)),Some(CallCheckValue::GuestTableBase),8) => return true,
            _ => return false
            }
        }
    }
    false
}

impl CallAnalyzer{
    pub fn aeval_unop(&self, in_state : &CallCheckLattice, value : &Value) -> CallCheckValueLattice{
        match value{
                Value::Mem(memsize, memargs) => 
                    if is_table_size(in_state, memargs){
                        return CallCheckValueLattice{ v : Some(CallCheckValue::TableSize)} 
                    }
                    else if is_fn_ptr(in_state, memargs){
                        return CallCheckValueLattice{ v : Some(CallCheckValue::FnPtr)} 
                    }
                    else if is_stack_access(value){
                        let offset = extract_stack_offset(memargs);
                        return in_state.stack.get(offset, memsize.to_u32()/8)
                    },

                Value::Reg(regnum, size) => return in_state.regs.get(regnum, size),
                    
                Value::Imm(_,_,immval) => 
                    if (*immval as u64) == self.metadata.guest_table_0 {
                        return CallCheckValueLattice{ v : Some(CallCheckValue::GuestTableBase)}
                    }
                    else if (*immval as u64) == self.metadata.lucet_tables {
                        return CallCheckValueLattice{ v : Some(CallCheckValue::LucetTablesBase)}
                }
            } 
            Default::default()   
        }

        //checked_val << 4
        pub fn aeval_binop(&self, in_state : &CallCheckLattice, opcode : &Binopcode, src1 : &Value, src2: &Value) -> CallCheckValueLattice{
            if let Binopcode::Shl = opcode{
                if let (Value::Reg(regnum1, size1), Value::Imm(_,_, 4)) = (src1,src2){
                    if let Some(CallCheckValue::CheckedVal) = in_state.regs.get(regnum1, size1).v{
                        return CallCheckValueLattice{ v : Some(CallCheckValue::PtrOffset(DAV::Checked))}
                    } 
                    else {
                        //TODO: use proper reaching def here / locidx here
                        let v  = ReachingDefnLattice {defs : BTreeSet::new()};
                        return CallCheckValueLattice{ v : Some(CallCheckValue::PtrOffset(DAV::Unchecked(v)))}
                    }
                }
            }   
            Default::default()
        }
    }