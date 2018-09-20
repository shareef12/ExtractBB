# LLVM Obfuscation Passes

## Setup
    apt install clang-6.0 llvm-6.0-dev

## Compilation
    clang-6.0 -c -emit-llvm test.c
    opt-6.0 --debug-pass=Structure -load build/lib/LLVMObfuscate.so -mem2reg -extractbb test.bc > test_opt.bc
    clang-6.0 test_opt.bc
