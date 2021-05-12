pub mod analyses;
pub mod checkers;
pub mod lattices;
pub mod utils;
use crate::analyses::call_analyzer::CallAnalyzer;
use crate::analyses::heap_analyzer::HeapAnalyzer;
use crate::analyses::reaching_defs::{analyze_reaching_defs,ReachingDefnAnalyzer};
use crate::analyses::run_worklist;
use crate::analyses::stack_analyzer::StackAnalyzer;
use crate::checkers::call_checker::check_calls;
use crate::checkers::heap_checker::check_heap;
use crate::checkers::stack_checker::check_stack;
use crate::utils::ir_utils::has_indirect_calls;
use crate::utils::utils::{Compiler,fully_resolved_cfg,get_data};
use utils::utils::{load_metadata, load_program, wamr_get_native_addrs};
use clap::{App, Arg};
use serde_json;
use std::fs;
use std::panic;
use std::time::Instant;
use std::str::FromStr;
use yaxpeax_core::analyses::control_flow::check_cfg_integrity;

pub struct Config {
    module_path: String,
    _num_jobs: u32,
    output_path: String,
    has_output: bool,
    _quiet: bool,
    compiler: Compiler,
    funcs: Vec<u32>,
    globals_size: i64,
    call_table_size: i64,
}

fn run(config: Config) {
    let mut func_counter = 0;
    let mut info: Vec<(std::string::String, usize, f64, f64, f64, f64)> = vec![];
    let program = load_program(&config.module_path);

    println!("Loading Metadata");
    let metadata = load_metadata(&config.module_path, config.compiler, config.globals_size+config.call_table_size*4);
    let (x86_64_data, func_addrs, plt) = get_data(&config.module_path, &program, &config.funcs);
    let mut valid_funcs: Vec<u64> = func_addrs.clone().iter().map(|x| x.0).collect();
    if let Compiler::Wamr = metadata.compiler {
        // Wamr has a few special functions that shouldn't be verified, but should be call-able
        valid_funcs.extend(wamr_get_native_addrs(&program));
    }
    for (addr, func_name) in &func_addrs {
        println!("Generating CFG for {:?}", func_name);
        let start = Instant::now();
        let (cfg, irmap) = fully_resolved_cfg(&program, &x86_64_data.contexts, &metadata, *addr);
        func_counter += 1;
        println!("Analyzing: {:?}", func_name);
        check_cfg_integrity(&cfg.blocks, &cfg.graph);

        println!("Checking Heap Safety");
        let heap_start = Instant::now();
        let heap_analyzer = HeapAnalyzer {
            metadata: metadata.clone(),
        };
        let heap_result = run_worklist(&cfg, &irmap, &heap_analyzer);
        let heap_safe = check_heap(heap_result, &irmap, &heap_analyzer, &func_addrs);
        if !heap_safe {
            panic!("Not Heap Safe");
        }

        println!("Checking Stack Safety");
        let stack_start = Instant::now();
        let stack_analyzer = StackAnalyzer { 
            metadata: metadata.clone(),
        };
        let stack_result = run_worklist(&cfg, &irmap, &stack_analyzer);
        let stack_safe = check_stack(stack_result, &irmap, &stack_analyzer);
        if !stack_safe {
            panic!("Not Stack Safe");
        }

        let call_start = Instant::now();
        println!("Checking Call Safety");
        if has_indirect_calls(&irmap) {
            let reaching_defs = analyze_reaching_defs(&cfg, &irmap, &metadata);
            let call_analyzer = CallAnalyzer {
                metadata: metadata.clone(),
                reaching_defs: reaching_defs.clone(),
                reaching_analyzer: ReachingDefnAnalyzer {metadata: metadata.clone(), cfg: cfg.clone(), irmap: irmap.clone()},
            };
            let call_result = run_worklist(&cfg, &irmap, &call_analyzer);
            let call_safe = check_calls(call_result, &irmap, &call_analyzer, &valid_funcs, &plt);
            if !call_safe {
                panic!("Not Call Safe");
            }

        }
        let end = Instant::now();
        info.push((
            func_name.to_string(),
            cfg.blocks.len(),
            (heap_start - start).as_secs_f64(),
            (stack_start - heap_start).as_secs_f64(),
            (call_start - stack_start).as_secs_f64(),
            (end - call_start).as_secs_f64(),
        ));
        println!(
            "Verified {:?} at {:?} blocks. CFG: {:?}s Stack: {:?}s Heap: {:?}s Calls: {:?}s",
            func_name,
            cfg.blocks.len(),
            (heap_start - start).as_secs_f64(),
            (stack_start - heap_start).as_secs_f64(),
            (call_start - stack_start).as_secs_f64(),
            (end - call_start).as_secs_f64()
        );
    }
    if config.has_output {
        let data = serde_json::to_string(&info).unwrap();
        println!("Dumping Stats to {}", config.output_path);
        fs::write(config.output_path, data).expect("Unable to write file");
    }

    let mut total_cfg_time = 0.0;
    let mut total_heap_time = 0.0;
    let mut total_stack_time = 0.0;
    let mut total_call_time = 0.0;
    for (_, _, cfg_time, heap_time, stack_time, call_time) in &info {
        total_cfg_time += cfg_time;
        total_heap_time += heap_time;
        total_stack_time += stack_time;
        total_call_time += call_time;
    }
    println!("Verified {:?} functions", func_counter);
    println!(
        "Total time = {:?}s CFG: {:?} Heap: {:?}s Stack: {:?}s Call: {:?}s",
        total_cfg_time + total_heap_time + total_stack_time + total_call_time,
        total_cfg_time,
        total_heap_time,
        total_stack_time,
        total_call_time
    );
    println!("Done!");
}

fn main() {
    let matches = App::new("VeriWasm")
        .version("0.1.0")
        .about("Validates safety of native Wasm code")
        .arg(
            Arg::with_name("module path")
                .short("i")
                .takes_value(true)
                .help("path to native Wasm module to validate")
                .required(true),
        )
        .arg(
            Arg::with_name("jobs")
                .short("j")
                .long("jobs")
                .takes_value(true)
                .help("Number of parallel threads (default 1)"),
        )
        .arg(
            Arg::with_name("stats output path")
                .short("o")
                .long("output")
                .takes_value(true)
                .help("Path to output stats file"),
        )
        .arg(Arg::with_name("quiet").short("q").long("quiet"))
        .arg(
            Arg::with_name("wamr")
                .short("w")
                .long("wamr")
                .help("Enables parsing and analysis of Wasm Micro Runtime binaries (WAMR)")
        )
        .arg(
            Arg::with_name("trusted")
                .short("t")
                .takes_value(true)
                .help("Comma-separated list of function numbers to trust (WAMR-only)"),
        )
        .arg(
            Arg::with_name("globals")
                .short("g")
                .takes_value(true)
                .help("Size of global data in memory (WAMR-only)"),
        )
        .arg(
            Arg::with_name("calls")
                .short("c")
                .takes_value(true)
                .help("# of functions in the indirect call table (WAMR-only)"),
        )
        .get_matches();

    let module_path = matches.value_of("module path").unwrap();
    let num_jobs_opt = matches.value_of("jobs");
    let output_path = matches.value_of("stats output path").unwrap_or("");
    let num_jobs = num_jobs_opt
        .map(|s| s.parse::<u32>().unwrap_or(1))
        .unwrap_or(1);
    let quiet = matches.is_present("quiet");
    let wamr = matches.is_present("wamr");
    let compiler: Compiler;
    let funcs: Vec<u32>;
    if wamr {
        compiler = Compiler::Wamr;
        if let Some(func_str) = matches.value_of("trusted") {
            funcs = func_str.split(",").map(|s| u32::from_str(s).unwrap()).collect();
        } else {
            funcs = vec![];
        }
    } else {
        compiler = Compiler::Lucet;
        funcs = vec![];
    }
    let globals_size_opt = matches.value_of("globals");
    let globals_size = globals_size_opt
        .map(|s| s.parse::<i64>().unwrap_or(-1))
        .unwrap_or(-1);
    let call_table_size_opt = matches.value_of("calls");
    let call_table_size = call_table_size_opt
        .map(|s| s.parse::<i64>().unwrap_or(-1))
        .unwrap_or(-1);

    let has_output = if output_path == "" { false } else { true };

    let config = Config {
        module_path: module_path.to_string(),
        _num_jobs: num_jobs,
        output_path: output_path.to_string(),
        has_output: has_output,
        _quiet: quiet,
        compiler: compiler,
        funcs: funcs,
        globals_size: globals_size,
        call_table_size: call_table_size,
    };

    run(config);
}
