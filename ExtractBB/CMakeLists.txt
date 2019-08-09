add_llvm_library(LLVMExtractBB MODULE
    Extract.cpp)

add_llvm_library(LLVMExtractInst MODULE
    Extract.cpp)
target_compile_definitions(LLVMExtractInst PRIVATE "-DSPLIT_BASICBLOCKS")
