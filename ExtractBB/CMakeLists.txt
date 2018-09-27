add_llvm_loadable_module(LLVMExtractBB
    Extract.cpp)

add_llvm_loadable_module(LLVMExtractInst
    Extract.cpp)
target_compile_definitions(LLVMExtractInst PRIVATE "-DSPLIT_BASICBLOCKS")
