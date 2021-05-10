use crate::analyses::jump_analyzer::SwitchAnalyzer;
use crate::analyses::{AbstractAnalyzer, AnalysisResult};
use crate::lattices::reachingdefslattice::LocIdx;
use crate::lattices::switchlattice::{SwitchLattice, SwitchValue, SwitchValueLattice};
use crate::utils::lifter::{IRMap, Stmt, Value, MemArgs, MemArg};
use crate::utils::utils::Compiler;
use std::collections::HashMap;
use yaxpeax_core::memory::repr::process::ModuleData;
use yaxpeax_core::memory::MemoryRepr;

fn load_target(program: &ModuleData, addr: u64) -> i64 {
    let b0 = program.read(addr).unwrap() as u32;
    let b1 = (program.read(addr + 1).unwrap() as u32) << 8;
    let b2 = (program.read(addr + 2).unwrap() as u32) << 16;
    let b3 = (program.read(addr + 3).unwrap() as u32) << 24;
    (b0 + b1 + b2 + b3) as i64
}

fn extract_jmp_targets(program: &ModuleData, aval: &SwitchValueLattice, compiler: Compiler) -> Vec<i64> {
    let mut targets: Vec<i64> = Vec::new();
    match aval.v {
        Some(SwitchValue::JmpTarget(base, upper_bound)) => {
            for idx in 0..upper_bound {
                let addr = match compiler {
                    Compiler::Lucet => base + idx * 4,
                    Compiler::Wamr => base + idx * 8, 
                };
                let target = load_target(program, addr.into());
                let resolved_target = match compiler {
                    Compiler::Lucet => ((base as i32) + (target as i32)) as i64,
                    Compiler::Wamr => target,
                };

                targets.push(resolved_target);
            }
        }
        _ => panic!("Jump Targets Broken, target = {:?}", aval.v),
    }
    targets
}

fn wamr_resolve_indirect_jump(program: &ModuleData,
                              state: &mut SwitchLattice, 
                              switch_targets: &mut HashMap<u64, Vec<i64>>,
                              addr: &u64,
                              memargs: &MemArgs) {
    match memargs {
        MemArgs::MemScale(base, disp, scale) => {
            if let MemArg::Imm(_, _, baseval) = base {
                if let MemArg::Reg(regnum, regsize) = disp {
                    if let MemArg::Imm(_, _, scaleval) = scale {
                        let aval = state.regs.get(regnum, regsize);
                        if let Some(SwitchValue::UpperBound(bound)) = aval.v {
                            let jmpbase = *baseval as u32;
                            assert!(*scaleval == 8, "Illegal scale value in indirect jump!");
                            println!("recognized jump with base {:x} and bound {}!", jmpbase, bound);
                            let jmpbound = SwitchValueLattice::new(SwitchValue::JmpTarget(jmpbase, bound));
                            let targets = extract_jmp_targets(program, &jmpbound, Compiler::Wamr);
                            switch_targets.insert(*addr, targets);
                        } else {
                            panic!("Scaled jump with unbounded register!");
                        }
                    } else {
                        panic!("Scaled jump with no immediate scaling!");
                    }
                } else {
                    panic!("Scaled jump with no register displacement!");
                }
            } else {
                panic!("Scaled jump with no immediate base!");
            }
        },
        _ => panic!("Unrecognized jump!"),
    }
}

// addr -> vec of targets
pub fn resolve_jumps(
    program: &ModuleData,
    result: AnalysisResult<SwitchLattice>,
    irmap: &IRMap,
    analyzer: &SwitchAnalyzer,
) -> HashMap<u64, Vec<i64>> {
    let mut switch_targets: HashMap<u64, Vec<i64>> = HashMap::new();

    for (block_addr, mut state) in result.clone() {
        for (addr, ir_stmts) in irmap.get(&block_addr).unwrap() {
            for (idx, ir_stmt) in ir_stmts.iter().enumerate() {
                analyzer.aexec(
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

    for (block_addr, mut state) in result {
        for (addr, ir_stmts) in irmap.get(&block_addr).unwrap() {
            for (idx, ir_stmt) in ir_stmts.iter().enumerate() {
                match ir_stmt {
                    Stmt::Branch(_, Value::Reg(regnum, regsize)) => {
                        let aval = state.regs.get(regnum, regsize);
                        let targets = extract_jmp_targets(program, &aval, Compiler::Lucet);
                        switch_targets.insert(*addr, targets);
                    }
                    Stmt::Branch(_, Value::Mem(_, memargs)) => {
                        match analyzer.compiler() {
                            Compiler::Lucet => panic!("Illegal Jump!"),
                            Compiler::Wamr => wamr_resolve_indirect_jump(program, &mut state, &mut switch_targets, addr, memargs),
                        }
                    }
                    _ => (),
                }

                analyzer.aexec(
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
    switch_targets
}
