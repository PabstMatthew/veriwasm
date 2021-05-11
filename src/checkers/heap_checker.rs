use crate::analyses::heap_analyzer::HeapAnalyzer;
use crate::analyses::{AbstractAnalyzer, AnalysisResult};
use crate::checkers::Checker;
use crate::utils::ir_utils::{is_mem_access, is_stack_access};
use crate::lattices::heaplattice::{HeapLattice, HeapValue};
use crate::lattices::heaplattice::{WAMR_MODULEINSTANCE_OFFSET, 
                                   WAMR_HEAPBASE_OFFSET, WAMR_EXCEPTION_OFFSET, WAMR_MEMBOUNDS_OFFSET, 
                                   WAMR_GLOBALSBASE_OFFSET,
                                   WAMR_FUNCTYPE_OFFSET, WAMR_FUNCPTRS_OFFSET, WAMR_FUNCINDS_OFFSET,
                                   WAMR_PAGECNT_OFFSET};
use crate::lattices::reachingdefslattice::LocIdx;
use crate::utils::lifter::{IRMap, MemArg, MemArgs, Stmt, ValSize, Value};
use crate::utils::utils::Compiler;

pub struct HeapChecker<'a> {
    irmap: &'a IRMap,
    analyzer: &'a HeapAnalyzer,
    func_addrs: &'a Vec<(u64, std::string::String)>,
}

pub fn check_heap(
    result: AnalysisResult<HeapLattice>,
    irmap: &IRMap,
    analyzer: &HeapAnalyzer,
    func_addrs: &Vec<(u64, std::string::String)>,
) -> bool {
    HeapChecker {
        irmap: irmap,
        analyzer: analyzer,
        func_addrs: func_addrs,
    }
    .check(result)
}

impl Checker<HeapLattice> for HeapChecker<'_> {
    fn check(&self, result: AnalysisResult<HeapLattice>) -> bool {
        self.check_state_at_statements(result)
    }

    fn irmap(&self) -> &IRMap {
        self.irmap
    }
    fn aexec(&self, state: &mut HeapLattice, ir_stmt: &Stmt, loc: &LocIdx) {
        self.analyzer.aexec(state, ir_stmt, loc)
    }

    fn check_statement(&self, state: &HeapLattice, ir_stmt: &Stmt, _loc_idx: &LocIdx) -> bool {
        match ir_stmt {
            //1. Check that at each call rdi has the expected value
            Stmt::Call(target) => {
                match self.analyzer.metadata.compiler {
                    Compiler::Lucet => {
                        // For Lucet, this means rdi points to the HeapBase
                        match state.regs.rdi.v {
                            Some(HeapValue::HeapBase) => (),
                            _ => {
                                println!("Call failure {:?}", state.stack.get(0, 8));
                                return false;
                            }
                        }
                    },
                    Compiler::Wamr => {
                        // For Wamr, this means rdi points to the current ExecEnv
                        match state.regs.rdi.v {
                            Some(HeapValue::WamrExecEnv) => (),
                            _ => {
                                if let Value::Imm(_, _, addr) = target {
                                    // handle the exception of calling trusted functions like
                                    // aot_invoke_native and aot_enlarge_memory
                                    for (a, _) in self.func_addrs {
                                        if (*addr as u64) == *a {
                                            println!("Called aot function without correct value in %rdi!");
                                            return false;
                                        }
                                    }
                                } else {
                                    println!("Invalid call instruction: {:?}", ir_stmt);
                                    return false;
                                }
                            }
                        }
                    },
                }
            }
            //2. Check that all load and store are safe
            Stmt::Unop(_, dst, src) => {
                if is_mem_access(dst) && !self.check_mem_access(state, dst){
                    return false;
                }
                //stack read: probestack <= stackgrowth + c < 8K
                if is_mem_access(src) && !self.check_mem_access(state, src){
                    return false;
                }
            }

            Stmt::Binop(_, dst, src1, src2) => {
                if is_mem_access(dst) && !self.check_mem_access(state, dst){
                    return false;
                }
                if is_mem_access(src1) && !self.check_mem_access(state, src1){
                    return false;
                }
                if is_mem_access(src2) && !self.check_mem_access(state, src2){
                    return false;
                }
            }
            Stmt::Clear(dst, srcs) => {
                if is_mem_access(dst) && !self.check_mem_access(state, dst){
                    return false;
                }
                for src in srcs {
                    if is_mem_access(src) && !self.check_mem_access(state, src){
                        return false;
                    }
                }
            }
            _ => (),
        }
        true
    }
}

impl HeapChecker<'_> {
    fn check_global_access(&self, state: &HeapLattice, access: &Value) -> bool {
        match self.analyzer.compiler() {
            Compiler::Lucet => {
                if let Value::Mem(_, memargs) = access {
                    match memargs {
                        MemArgs::Mem1Arg(MemArg::Reg(regnum, ValSize::Size64)) => {
                            if let Some(HeapValue::GlobalsBase) = state.regs.get(regnum, &ValSize::Size64).v
                            {
                                return true;
                            }
                        }
                        MemArgs::Mem2Args(
                            MemArg::Reg(regnum, ValSize::Size64),
                            MemArg::Imm(_, _, globals_offset),
                        ) => {
                            if let Some(HeapValue::GlobalsBase) = state.regs.get(regnum, &ValSize::Size64).v
                            {
                                return *globals_offset <= 4096;
                            }
                        }
                        _ => return false,
                    }
                }
                false
            }
            Compiler::Wamr => {
                if let Value::Mem(memsize, memargs) = access {
                    match memargs {
                        MemArgs::Mem1Arg(MemArg::Reg(regnum, ValSize::Size64)) => {
                            // accessing the base global variable memory
                            if let Some(HeapValue::GlobalsBase) = state.regs.get(regnum, &ValSize::Size64).v {
                                return ((memsize.to_u32()/8) as i64) <= self.analyzer.metadata.globals_size;
                            }
                        },
                        MemArgs::Mem2Args(
                            MemArg::Reg(regnum, ValSize::Size64),
                            MemArg::Imm(_, _, globals_offset),
                        ) => {
                            // accessing an offset from global variable memory
                            if let Some(HeapValue::GlobalsBase) = state.regs.get(regnum, &ValSize::Size64).v {
                                return (*globals_offset+((memsize.to_u32()/8) as i64)) <= self.analyzer.metadata.globals_size;
                            }
                        },
                        _ => return false,
                    }
                }
                false
            },
        }
    }

    fn check_heap_access(&self, state: &HeapLattice, access: &Value) -> bool {
        if let Value::Mem(_, memargs) = access {
            match memargs {
                // if only arg is heapbase
                MemArgs::Mem1Arg(MemArg::Reg(regnum, ValSize::Size64)) => {
                    if let Some(HeapValue::HeapBase) = state.regs.get(regnum, &ValSize::Size64).v {
                        return true;
                    }
                }
                // if arg1 is heapbase and arg2 is bounded
                MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), memarg2) => {
                    if let Some(HeapValue::HeapBase) = state.regs.get(regnum, &ValSize::Size64).v {
                        match memarg2 {
                            MemArg::Reg(regnum2, size2) => {
                                if let Some(HeapValue::Bounded4GB) =
                                    state.regs.get(regnum2, size2).v
                                {
                                    return true;
                                }
                            }
                            MemArg::Imm(_, _, v) => return *v <= 0xffffffff,
                        }
                    }
                }
                // if arg1 is heapbase and arg2 and arg3 are bounded ||
                // if arg1 is bounded and arg1 and arg3 are bounded
                MemArgs::Mem3Args(memarg1, memarg2, memarg3) => {
                    // swizzle the args depending on which register is HeapBase
                    let mut arg1 = memarg2;
                    let arg2 = memarg3;
                    let mut reg: Option<&u8> = None;
                    if let MemArg::Reg(reg1, ValSize::Size64) = memarg1 {
                        if let Some(HeapValue::HeapBase) = state.regs.get(reg1, &ValSize::Size64).v {
                            reg = Some(reg1);
                        }
                    } 
                    if let MemArg::Reg(reg2, ValSize::Size64) = memarg2 {
                        if let Some(HeapValue::HeapBase) = state.regs.get(reg2, &ValSize::Size64).v {
                            reg = Some(reg2);
                            arg1 = memarg1;
                        }
                    }
                    // check that the access is bounded
                    if let Some(regnum) = reg {
                        if let Some(HeapValue::HeapBase) = state.regs.get(regnum, &ValSize::Size64).v {
                            match (arg1, arg2) {
                                (MemArg::Reg(regnum2, size2), MemArg::Imm(_, _, v))
                                | (MemArg::Imm(_, _, v), MemArg::Reg(regnum2, size2)) => {
                                    if let Some(HeapValue::Bounded4GB) =
                                        state.regs.get(regnum2, size2).v
                                    {
                                        return *v <= 0xffffffff;
                                    }
                                }
                                (MemArg::Reg(regnum2, size2), MemArg::Reg(regnum3, size3)) => {
                                    if let (Some(HeapValue::Bounded4GB), Some(HeapValue::Bounded4GB)) = (
                                        state.regs.get(regnum2, size2).v,
                                        state.regs.get(regnum3, size3).v,
                                    ) {
                                        return true;
                                    }
                                }
                                _ => (),
                            }
                        }
                    }
                },
                _ => return false,
            }
        }
        false
    }

    fn lucet_check_metadata_access(&self, state: &HeapLattice, access: &Value) -> bool {
        if let Value::Mem(_size, memargs) = access {
            match memargs{
                //Case 1: mem[globals_base]
                MemArgs::Mem1Arg(MemArg::Reg(regnum,ValSize::Size64)) => {
                    if let  Some(HeapValue::GlobalsBase) = state.regs.get(regnum,&ValSize::Size64).v {
                        return true
                    }
                },
                //Case 2: mem[lucet_tables + 8]
                MemArgs::Mem2Args(MemArg::Reg(regnum,ValSize::Size64), MemArg::Imm(_,_,8)) => {
                    if let Some(HeapValue::LucetTables) = state.regs.get(regnum,&ValSize::Size64).v{
                        return true
                    }
                },
                MemArgs::Mem2Args(MemArg::Reg(regnum1,ValSize::Size64), MemArg::Reg(regnum2,ValSize::Size64)) => {
                    if let Some(HeapValue::GuestTable0) = state.regs.get(regnum1,&ValSize::Size64).v{
                        return true
                    }
                    if let Some(HeapValue::GuestTable0) = state.regs.get(regnum2,&ValSize::Size64).v{
                        return true
                    }
                },
                MemArgs::Mem3Args(MemArg::Reg(regnum1,ValSize::Size64),MemArg::Reg(regnum2,ValSize::Size64), MemArg::Imm(_,_,8)) => {
                    match (state.regs.get(regnum1,&ValSize::Size64).v,state.regs.get(regnum2,&ValSize::Size64).v){
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

    fn wamr_check_metadata_access(&self, state: &HeapLattice, access: &Value) -> bool {
        if let Value::Mem(_size, memargs) = access {
            match memargs {
                //Case 1: mem[WamrExecEnv+WAMR_MODULEINSTANCE_OFFSET]
                MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), MemArg::Imm(_, _, WAMR_MODULEINSTANCE_OFFSET)) => {
                    if let Some(HeapValue::WamrExecEnv) = state.regs.get(regnum, &ValSize::Size64).v {
                        return true;
                    }
                },
                //Case 2: mem[WamrModuleInstance+WAMR_HEAPBASE_OFFSET]
                MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), MemArg::Imm(_, _, WAMR_HEAPBASE_OFFSET)) => {
                    if let Some(HeapValue::WamrModuleInstance) = state.regs.get(regnum, &ValSize::Size64).v {
                        return true;
                    }
                },
                //Case 3: mem[WamrModuleInstance+WAMR_EXCEPTION_OFFSET]
                MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), MemArg::Imm(_, _, WAMR_EXCEPTION_OFFSET)) => {
                    if let Some(HeapValue::WamrModuleInstance) = state.regs.get(regnum, &ValSize::Size64).v {
                        return true;
                    }
                },
                //Case 4: mem[WamrModuleInstance+WAMR_MEMBOUNDS_OFFSET]
                MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), MemArg::Imm(_, _, WAMR_MEMBOUNDS_OFFSET)) => {
                    if let Some(HeapValue::WamrModuleInstance) = state.regs.get(regnum, &ValSize::Size64).v {
                        return true;
                    }
                },
                //Case 5: mem[WamrExecEnv+WAMR_GLOBALSBASE_OFFSET]
                MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), MemArg::Imm(_, _, WAMR_GLOBALSBASE_OFFSET)) => {
                    if let Some(HeapValue::WamrExecEnv) = state.regs.get(regnum, &ValSize::Size64).v {
                        return true;
                    }
                },
                //Case 6: mem[WamrModuleInstance+WAMR_FUNCTYPE_OFFSET]
                MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), MemArg::Imm(_, _, WAMR_FUNCTYPE_OFFSET)) => {
                    if let Some(HeapValue::WamrModuleInstance) = state.regs.get(regnum, &ValSize::Size64).v {
                        return true;
                    }
                },
                //Case 7: mem[WamrModuleInstance+WAMR_FUNCPTRS_OFFSET]
                MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), MemArg::Imm(_, _, WAMR_FUNCPTRS_OFFSET)) => {
                    if let Some(HeapValue::WamrModuleInstance) = state.regs.get(regnum, &ValSize::Size64).v {
                        return true;
                    }
                },
                //Case 8: mem[WamrModuleInstance+WAMR_PAGECNT_OFFSET]
                MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), MemArg::Imm(_, _, WAMR_PAGECNT_OFFSET)) => {
                    if let Some(HeapValue::WamrModuleInstance) = state.regs.get(regnum, &ValSize::Size64).v {
                        return true;
                    }
                },
                _ => return false,
            }
        }
        false
    }

    fn check_metadata_access(&self, state: &HeapLattice, access: &Value) -> bool {
        match self.analyzer.metadata.compiler {
            Compiler::Lucet => return self.lucet_check_metadata_access(state, access),
            Compiler::Wamr => return self.wamr_check_metadata_access(state, access),
        }
    }

    fn check_jump_table_access(&self, state: &HeapLattice, access: &Value) -> bool {
        match self.analyzer.metadata.compiler {
            Compiler::Lucet => {
                if let Value::Mem(_size, memargs) = access {
                    match memargs {
                        MemArgs::MemScale(_, _, MemArg::Imm(_, _, 4)) => return true,
                        _ => return false,
                    }
                }
                false
            },
            Compiler::Wamr => {
                if let Value::Mem(_size, memargs) = access {
                    match memargs {
                        // Case 1: an access to the table of function indexes
                        MemArgs::Mem2Args(MemArg::Reg(regnum, ValSize::Size64), MemArg::Imm(_, _, immval)) => {
                            if let Some(HeapValue::WamrModuleInstance) = state.regs.get(regnum, &ValSize::Size64).v {
                                if *immval >= WAMR_FUNCINDS_OFFSET || *immval == WAMR_FUNCINDS_OFFSET-4 {
                                    // responsibility of call checker to check this is in-bounds
                                    return true;
                                }
                            }
                        },
                        MemArgs::MemScaleDisp(MemArg::Reg(regnum, ValSize::Size64),
                                              MemArg::Reg(_, _), MemArg::Imm(_, _, 4),
                                              MemArg::Imm(_, _, disp)) => {
                            if let Some(HeapValue::WamrModuleInstance) = state.regs.get(regnum, &ValSize::Size64).v {
                                if *disp >= 0x1a8 {
                                    // responsibility of call checker to check this is in-bounds
                                    return true;
                                }
                            }
                        }
                        // Case 2: an access to the table of function types
                        MemArgs::MemScale(MemArg::Reg(regnum, ValSize::Size64), 
                                          MemArg::Reg(_, ValSize::Size64), MemArg::Imm(_, _, 4)) => {
                            if let Some(HeapValue::WamrFuncTypeTable) = state.regs.get(regnum, &ValSize::Size64).v {
                                // responsibility of call checker to check this is a valid index
                                return true;
                            }
                        },
                        // Case 3: an access to the table of function pointers
                        MemArgs::MemScale(MemArg::Reg(regnum, ValSize::Size64), 
                                          MemArg::Reg(_, ValSize::Size64), MemArg::Imm(_, _, 8)) => {
                            if let Some(HeapValue::WamrFuncPtrsTable) = state.regs.get(regnum, &ValSize::Size64).v {
                                // responsibility of call checker to check this is a valid index
                                return true;
                            }
                        },
                        _ => return false,
                    }
                }
                false
            },
        }
    }

    fn check_mem_access(&self, state: &HeapLattice, access: &Value) -> bool {
        // Case 1: its a stack access
        if is_stack_access(access) {
            return true;
        }
        // Case 2: its a heap access
        if self.check_heap_access(state, access) {
            return true;
        };
        // Case 3: its a metadata access
        if self.check_metadata_access(state, access) {
            return true;
        };
        // Case 4: its a globals access
        if self.check_global_access(state, access) {
            return true;
        };
        // Case 5: Jump table access
        if self.check_jump_table_access(state, access) {
            return true;
        };
        // Case 6: its unknown
        println!("None of the memory accesses!");
        print_mem_access(state, access);
        return false;
    }
}

pub fn memarg_repr(state: &HeapLattice, memarg: &MemArg) -> String {
    match memarg {
        MemArg::Reg(regnum, size) => format!("r{:?}: {:?}", regnum, state.regs.get(regnum, size).v),
        MemArg::Imm(_, _, x) => format!("{:?}", x),
    }
}

pub fn print_mem_access(state: &HeapLattice, access: &Value) {
    if let Value::Mem(_, memargs) = access {
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
}
