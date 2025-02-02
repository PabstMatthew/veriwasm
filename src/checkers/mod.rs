use crate::analyses::AnalysisResult;
use crate::lattices::reachingdefslattice::LocIdx;
use crate::lattices::Lattice;
use crate::utils::lifter::IRMap;
use crate::utils::lifter::Stmt;

pub mod call_checker;
pub mod heap_checker;
pub mod jump_resolver;
pub mod stack_checker;

pub trait Checker<State: Lattice + Clone> {
    fn check(&self, result: AnalysisResult<State>) -> bool;
    fn irmap(&self) -> &IRMap;
    fn aexec(&self, state: &mut State, ir_stmt: &Stmt, loc: &LocIdx);

    fn check_state_at_statements(&self, result: AnalysisResult<State>) -> bool {
        for (block_addr, mut state) in result {
            for (addr, ir_stmts) in self.irmap().get(&block_addr).unwrap() {
                //println!("analyzing block at {:x}", addr);
                for (idx, ir_stmt) in ir_stmts.iter().enumerate() {
                    //println!("checking statement: {:?}", ir_stmt);
                    if !self.check_statement(
                        &state,
                        ir_stmt,
                        &LocIdx {
                            addr: *addr,
                            idx: idx as u32,
                        },
                    ) {
                        return false;
                    }
                    self.aexec(
                        &mut state,
                        ir_stmt,
                        &LocIdx {
                            addr: *addr,
                            idx: idx as u32,
                        },
                    );
                }
            }
        }
        true
    }
    fn check_statement(&self, state: &State, ir_stmt: &Stmt, loc_idx: &LocIdx) -> bool;
}
