# VeriWamr: SFI safety for native-compiled Wasm (using the Wasm Micro-Runtime!)

This repository extends the [VeriWasm](https://github.com/PLSysSec/veriwasm) tool to verify binaries compiled by the [Wasm Micro-Runtime](https://github.com/bytecodealliance/wasm-micro-runtime).
Here's the paper describing how the tool works for the Lucet compiler: [Доверя́й, но проверя́й: SFI safety for native-compiled Wasm](http://cseweb.ucsd.edu/~dstefan/pubs/johnson:2021:veriwasm.pdf).  
  
## Build VeriWasm

You first need to install several dependencies:

- git
- Rust
- nasm (to compile test cases)
- gcc (to compile test cases)
- python3 (for scripts)

Once you have these, you can build VeriWasm:

```bash
git submodule update --init --recursive
cargo build --release
```

## Run VeriWasm

To run VeriWasm on your own binaries, you just need to point it to the module you want to check:

```bash
cargo run --release -- -i <input path> --wamr
```

Usage:  

```
VeriWasm 0.1.0
Validates safety of native Wasm code

USAGE:
    veriwasm [FLAGS] [OPTIONS] -i <module path>

FLAGS:
    -h, --help       Prints help information
    -q, --quiet      
    -V, --version    Prints version information
    -w, --wamr       Enables parsing and analysis of Wasm Micro Runtime binaries (WAMR)

OPTIONS:
    -c <calls>                          # of functions in the indirect call table (WAMR-only)
    -g <globals>                        Size of global data in memory (WAMR-only)
    -j, --jobs <jobs>                   Number of parallel threads (default 1)
    -i <module path>                    path to native Wasm module to validate
    -o, --output <stats output path>    Path to output stats file
    -t <trusted>                        Comma-separated list of function numbers to trust (WAMR-only)
```

## Related repos
- [A fork of the Wasm testsuite that I used to test the verifier's precision](https://github.com/PabstMatthew/testsuite)
- [A fork of the yaxpeax-core Rust module to which I added more support for Wamr-specific instruction](https://github.com/PabstMatthew/yaxpeax-core)
- [A similar fork for yaxpeax-x86](https://github.com/PabstMatthew/yaxpeax-x86)

## Limitations
- No support for verifying SIMD/AVX instructions.
- Because of WAMR's design, the verifier is forced to trust that the compiler correctly sets up the contents of indirect call index table.

