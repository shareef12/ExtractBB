# LLVM Obfuscation Passes

## Setup
    apt install clang-6.0 llvm-6.0-dev

## Compilation
    clang-6.0 -Xclang -load -Xclang build/lib/LLVMExtractBB.so test.c

    clang-6.0 -c -emit-llvm test.c
    opt-6.0 -load build/lib/LLVMExtractBB.so -extractbb test.bc > test_opt.bc
    opt-6.0 -debug -load release_601/build/lib/LLVMExtractBB.so -extractbb test.bc > test_opt.bc
    opt-6.0 -debug-only=extractbb -load release_601/build/lib/LLVMExtractBB.so -extractbb test.bc > test_opt.bc
    opt-6.0 --debug-pass=Structure -load build/lib/LLVMExtractBB.so -extractbb test.bc > test_opt.bc
    clang-6.0 test_opt.bc
