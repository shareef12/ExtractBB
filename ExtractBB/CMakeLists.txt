# This is a work-around for an LLVM bug in the llvm-8-dev package that will
# cause a segmentation fault during llvm_shutdown(). There is an issue with
# LLVM's implementation of ManagedStatic that will cause our plugin to be
# unloaded before our pass is cleaned up. This will result in a call through a
# dangling pointer to our unloaded library. Note that this issue only manifests
# when using RegisterStandardPasses with an out-of-tree build.
#
# This issue is mentioned in a few places:
#   http://lists.llvm.org/pipermail/llvm-dev/2017-September/117566.html
#   https://github.com/sampsyo/llvm-pass-skeleton/issues/7
#   https://bugs.llvm.org/show_bug.cgi?id=34573
#   https://bugs.llvm.org/show_bug.cgi?id=39321 https://reviews.llvm.org/D33515
set(CMAKE_MODULE_LINKER_FLAGS "${CMAKE_MODULE_LINKER_FLAGS} -Wl,-znodelete")

add_llvm_library(LLVMExtractBB MODULE
    Extract.cpp)

add_llvm_library(LLVMExtractInst MODULE
    Extract.cpp)
target_compile_definitions(LLVMExtractInst PRIVATE "-DSPLIT_BASICBLOCKS")
