use yaxpeax_core::analyses::control_flow::VW_CFG;
use crate::analyses::AnalysisResult;
use yaxpeax_core::analyses::control_flow::ControlFlowGraph;
use crate::lattices::reachingdefslattice::{ReachLattice, singleton, LocIdx};
use crate::analyses::{AbstractAnalyzer, run_worklist};
use crate::lifter::{IRMap, Stmt};
use crate::utils::{LucetMetadata};
use crate::lattices::VarState;

//Top level function
pub fn analyze_reaching_defs(cfg : &VW_CFG, irmap : &IRMap, _metadata : LucetMetadata) -> AnalysisResult<ReachLattice>{
    run_worklist(cfg, irmap, &ReachingDefnAnalyzer{})    
}

pub struct ReachingDefnAnalyzer{}

impl AbstractAnalyzer<ReachLattice> for ReachingDefnAnalyzer {
    fn aexec(&self, in_state : &mut ReachLattice, ir_instr : &Stmt, loc_idx : &LocIdx) -> () {
        match ir_instr{
            Stmt::Clear(dst) => in_state.set(dst, singleton(loc_idx.clone())),
            Stmt::Unop(_, dst, _) =>  in_state.set(dst, singleton(loc_idx.clone())),
            Stmt::Binop(opcode, dst, src1, src2) =>  {
                in_state.adjust_stack_offset(opcode, dst, src1, src2);  
                in_state.set(dst, singleton(loc_idx.clone()))
            },
            Stmt::Call(_) => in_state.regs.clear_regs(),
            _ => ()
        }
    }
}
