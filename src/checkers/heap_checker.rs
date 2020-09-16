use crate::ir_utils::get_imm_mem_offset;
use crate::ir_utils::is_stack_access;
use crate::ir_utils::is_mem_access;
use crate::lifter::{Stmt, Value, ValSize, MemArg, MemArgs};
use crate::lattices::reachingdefslattice::LocIdx;
use crate::analyses::heap_analyzer::HeapAnalyzer;
use crate::lifter::IRMap;
use crate::checkers::Checker;
use crate::analyses::{AnalysisResult};
use crate::lattices::heaplattice::{HeapLattice, HeapValue};
use crate::analyses::AbstractAnalyzer;

pub struct HeapChecker<'a>{
    irmap : &'a  IRMap, 
    analyzer : &'a HeapAnalyzer
}

pub fn check_heap(result : AnalysisResult<HeapLattice>, 
    irmap : &IRMap, 
    analyzer : &HeapAnalyzer) -> bool{
    HeapChecker{irmap : irmap, analyzer : analyzer}.check(result)    
}

impl Checker<HeapLattice> for HeapChecker<'_> {
    fn check(&self, result : AnalysisResult<HeapLattice>) -> bool{
        self.check_state_at_statements(result)
    }

    //TODO: finish check_state
    fn check_state(&self, state : &HeapLattice) -> bool {
        true
    }
}

impl HeapChecker<'_> {
    fn check_state_at_statements(&self, result : AnalysisResult<HeapLattice>) -> bool{
        for (block_addr,mut state) in result {
            for (addr,ir_stmts) in self.irmap.get(&block_addr).unwrap(){
                for (idx,ir_stmt) in ir_stmts.iter().enumerate(){
                    self.analyzer.aexec(&mut state, ir_stmt, &LocIdx {addr : *addr, idx : idx as u32});
                    if !self.check_state(&state){
                        return false
                    }
                }
            }
        }
        true
    }
    
    fn check_global_access(&self, state : &HeapLattice, access: &Value) -> bool{
        if let Value::Mem(size, memargs) = access {
            match memargs{
                MemArgs::Mem1Arg(MemArg::Reg(regnum,ValSize::Size64)) => 
                    if let  Some(HeapValue::GlobalsBase) = state.regs.get(regnum).v { 
                        return true
                    }
                MemArgs::Mem2Args(MemArg::Reg(regnum,ValSize::Size64), MemArg::Imm(_,_,globals_offset)) => {
                    if let Some(HeapValue::GlobalsBase) = state.regs.get(regnum).v{    
                        return *globals_offset <= 4096
                    }
                },
                _ => return false
            }            
        }
        false
    }

    fn check_heap_access(&self, state : &HeapLattice, access: &Value) -> bool{
        if let Value::Mem(size, memargs) = access {
            match memargs{
                // if only arg is heapbase
                MemArgs::Mem1Arg(MemArg::Reg(regnum,ValSize::Size64)) => 
                    if let Some(HeapValue::HeapBase) = state.regs.get(regnum).v {
                        return true
                },
                // if arg1 is heapbase and arg2 is bounded
                MemArgs::Mem2Args(MemArg::Reg(regnum,ValSize::Size64),memarg2) => 
                if let Some(HeapValue::HeapBase) = state.regs.get(regnum).v {
                    match memarg2{
                        MemArg::Reg(regnum2, _) => 
                        if let Some(HeapValue::Bounded4GB) = state.regs.get(regnum2).v {
                            return true
                        },
                        MemArg::Imm(_,_,v) => return *v <= 0xffffffff 
                    }
                }
                // if arg1 is heapbase and arg2 and arg3 are bounded || 
                // if arg1 is bounded and arg1 and arg3 are bounded
                //TODO: allow second arg to be heapbase?
                MemArgs::Mem3Args(MemArg::Reg(regnum,ValSize::Size64),memarg2,memarg3) => 
                if let Some(HeapValue::HeapBase) = state.regs.get(regnum).v {
                    match (memarg2,memarg3){
                        (MemArg::Reg(regnum2, _),MemArg::Imm(_,_,v)) | (MemArg::Imm(_,_,v),MemArg::Reg(regnum2, _))=> 
                        if let Some(HeapValue::Bounded4GB) = state.regs.get(regnum2).v {
                            return *v <= 0xffffffff
                        },
                        (MemArg::Reg(regnum2, _),MemArg::Reg(regnum3, _)) => 
                            if let (Some(HeapValue::Bounded4GB),Some(HeapValue::Bounded4GB)) = (state.regs.get(regnum2).v,state.regs.get(regnum3).v){
                                return true
                            }
                        _ => () 
                    }
                },
                _ => return false
            }
        }
        false
    }

    fn check_metadata_access(&self, state : &HeapLattice, access: &Value) -> bool{
        if let Value::Mem(size, memargs) = access {
            match memargs{
                //Case 1: mem[globals_base]
                MemArgs::Mem1Arg(MemArg::Reg(regnum,ValSize::Size64)) => 
                    if let  Some(HeapValue::GlobalsBase) = state.regs.get(regnum).v { 
                        return true
                    }
                //Case 2: mem[lucet_tables + 8]
                MemArgs::Mem2Args(MemArg::Reg(regnum,ValSize::Size64), MemArg::Imm(_,_,8)) => {
                    if let Some(HeapValue::LucetTables) = state.regs.get(regnum).v{    
                        return true
                    }
                },
                MemArgs::Mem3Args(MemArg::Reg(regnum1,ValSize::Size64),MemArg::Reg(regnum2,ValSize::Size64), MemArg::Imm(_,_,8)) => {
                    match (state.regs.get(regnum1).v,state.regs.get(regnum2).v){
                        (Some(HeapValue::GuestTable0),_) => return true,
                        (_,Some(HeapValue::GuestTable0)) => return true,
                        _ => ()
                    }
                }
                _ => return false
            }       
        }
        false
    }

    fn check_mem_access(&self, state : &HeapLattice, access: &Value) -> bool{
        // Case 1: its a stack access
        if is_stack_access(access) { return true}
        // Case 2: its a heap access
        if self.check_heap_access(state, access){ return true };
        // Case 3: its a metadata access
        if self.check_heap_access(state, access){ return true };
        // Case 4: its a globals access
        if self.check_global_access(state, access){ return true };
        // Case 5: its unknown
        false
    }


    // TODO Complete
    fn check_statement(&self, state : &HeapLattice, ir_stmt : &Stmt) -> bool {
        match ir_stmt{
            //1. Check that at each call rdi = HeapBase
            Stmt::Call(_) => 
             match state.regs.rdi.v{
                 Some(HeapValue::HeapBase) => (),
                 _ => return false
             },
             //2. Check that all load and store are safe
             Stmt::Unop(_, dst, src) => 
             if is_mem_access(dst){
                if !self.check_mem_access(state, dst){return false}
            }
            //stack read: probestack <= stackgrowth + c < 8K
            else if is_mem_access(src) {
                if !self.check_mem_access(state, src){return false}
            },
             _ => ()
        }
        
        
        true
    }
}

