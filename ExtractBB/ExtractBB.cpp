/**
 * TODO:
 *  - Play around with different optimization settings to reduce memory accesses
 *      - Fix SIGSEGV on -Ox
 *  - Split basic blocks to create more functions
 *
 *  - Move alloca uses in a different basic block to the current basic block
 *
 * Not supported:
 *  - switch statements
 *  - indirect branches
 *  - exceptions/cleanup
 */

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include <cstdlib>
#include <memory>

#define DEBUG_TYPE "extractbb"

using namespace llvm;

namespace {

/**
 * @brief Structure used to represent the current state of a BasicBlock that
 *        is being extracted.
 * @member BB BasicBlock that's being extracted.
 * @member Func Extracted function. This is only valid after all parameters
 *         have been calculated.
 * @member params A map of values that will become input parameters for the
 *         extracted function. Each parameter maps to a list of Uses in the
 *         extracted function.
 */
struct BBContext {
    BasicBlock *BB;
    Function *Func;
    std::map<Value *, SmallVector<Use *, 4>> params;
};

typedef std::map<BasicBlock *, std::unique_ptr<BBContext>> BBMap;


/**
 * @brief Create a BBContext object. Populate params with Values used in the
 *        given basic block.
 *
 * Get the values used by instructions in this basic block. These values will
 * become the input parameters to an extracted function. This function will
 * also verify that all output values are only used within the current
 * BasicBlock.
 *
 * @return A BBContext with a partially initialized set of params.
 */
std::unique_ptr<BBContext> createBBContext(BasicBlock &BB) {
    std::unique_ptr<BBContext> ctx(new BBContext());
    ctx->BB = &BB;
    ctx->Func = nullptr;

    DEBUG(dbgs() << "  Basic block (name=" << BB.getName() << ") has "
                 << BB.size() << " instructions.\n");
    for (Instruction &I : BB) {
        DEBUG(dbgs() << "    inst: " << I << "\n");

        // ignore terminator instructions
        if (isa<TerminatorInst>(I)) {
            continue;
        }

        for (Use &U : I.operands()) {
            Value *value = U.get();

            // globals and constants don't need to become parameters.
            // llvm GlobalValue subclasses llvm::Constant.
            if (isa<Constant>(value)) {
                continue;
            }

            // values from the same basic block don't need to become
            // parameters.
            if (auto *VI = dyn_cast<Instruction>(value)) {
                if (VI->getParent() == &BB) {
                    continue;
                }
            }

            DEBUG(dbgs() << "      ");
            DEBUG(value->dump());

            if (ctx->params.count(value) == 0) {
                ctx->params[value] = std::move(SmallVector<Use *, 4>());
            }
            ctx->params[value].push_back(&U);
        }
    }

    return ctx;
}


/**
 * @brief Perform a recursive postorder traversal of the CFG in order to
 *        determine parameters for each extracted basic block function.
 *
 * Since we're doing a postorder traversal in a graph that may have loops,
 * there's no way to have a complete answer if a loop is detected (since the
 * already seen successor hasn't been populated yet). To fix this, the
 * traversal must be performed at least twice.
 *
 * @param BB Current BasicBlock to process.
 * @param bbMap Map of all BasicBlocks to their contexts. The goal of the
 *        traversal is to fully populate this map.
 * @param seenBB A set of all BasicBlocks seen so far during this recursive
 *        iteration. This variable is used to detect loops in the CFG and
 *        prevent infinite recursion.
 */
void visitBasicBlock(BasicBlock &BB,
                     BBMap &bbMap,
                     SmallPtrSet<BasicBlock *, 32> &seenBB) {
    // base case 1: BB terminator is a function terminator
    if (isa<ReturnInst>(BB.getTerminator())) {
        if (bbMap.count(&BB) == 0) {
            bbMap[&BB] = createBBContext(BB);
        }

        seenBB.erase(&BB);
        return;
    }

    // base case 2: loop detected
    if (seenBB.count(&BB) > 0) {
        return;
    }

    // recursive case: recurse to get params of children, then populate current
    // block.
    seenBB.insert(&BB);
    if (bbMap.count(&BB) == 0) {
        bbMap[&BB] = createBBContext(BB);
    }
    std::unique_ptr<BBContext> &ctx = bbMap[&BB];

    for (succ_iterator si = succ_begin(&BB), se = succ_end(&BB); si != se; si++) {
        // recurse to populate bbMap[succBB]
        visitBasicBlock(**si, bbMap, seenBB);

        // add succ params to this function params. succ params won't have
        // any Uses associated with them since there is no CallInst yet.
        std::unique_ptr<BBContext> &succCtx = bbMap[*si];
        for (auto it : succCtx->params) {
            Value *value = it.first;
            if (ctx->params.count(value) == 0) {
                ctx->params[value] = std::move(SmallVector<Use *, 4>());
            }
        }
    }

    seenBB.erase(&BB);
}


/**
 * @brief Extract a basic block into a function.
 * @param M Module to insert the function into.
 * @param ctx Context object containing information about the BasicBlock to
 *        extract.
 */
void extractBasicBlock(Module &M, BBContext &ctx) {
    // create the function
    SmallVector<Type *, 8> argsTy;
    for (auto it : ctx.params) {
        Value *value = it.first;
        argsTy.push_back(value->getType());
    }

    Type *retTy = ctx.BB->getParent()->getReturnType();
    FunctionType *funcTy = FunctionType::get(retTy, argsTy, false);

    SmallString<64> funcName(ctx.BB->getParent()->getName());
    funcName.append("_extracted_");
    funcName.append(ctx.BB->getName());
    ctx.Func = Function::Create(funcTy, GlobalValue::InternalLinkage, funcName.str(), &M);

    // move the basic block to the new function
    ctx.BB->removeFromParent();
    ctx.BB->insertInto(ctx.Func);
}


/**
 * @brief Helper function to create a CallInst to an extracted BasicBlock.
 * @param builder IRBuilder that should be used to insert instructions.
 * @param ctx Context for the current extracted function. This can be nullptr
 *        if the current function is not an extracted BasicBlock.
 * @param targetCtx Context representing the extracted BasicBlock that should
 *        be used as the call target.
 */
CallInst * createCallInst(IRBuilder<> &builder, BBContext *ctx,
                          std::unique_ptr<BBContext> &targetCtx) {
    // build argument array for the call from the child
    SmallVector<Value *, 8> args;
    for (auto it : targetCtx->params) {
        Value *value = it.first;
        args.push_back(value);
    }

    CallInst *callInst = builder.CreateCall(targetCtx->Func, args);

    // if this BasicBlock was extracted, add the new uses to the list
    // of uses for the arguments so it can be properly replaced later.
    if (ctx != nullptr) {
        for (Use &U : callInst->arg_operands()) {
            Value *value = U.get();
            ctx->params[value].push_back(&U);
        }
    }

    return callInst;
}


/**
 * @brief Fixup the terminator instruction for a BasicBlock. Since successor
 *        BasicBlocks are extracted to functions, we need to translate branches
 *        to calls.
 *
 * This function currently handles three cases:
 *  - ReturnInst or UnreachableInst: The terminator is a terminator for the
 *      original function. No action required.
 *  - Unconditional Branch: Replace the branch with a call to the branch target
 *      and a return.
 *  - Conditional Branch: Create two new BasicBlocks to replace the branch
 *      successors. For each block, insert a call to the original successor and
 *      branch to a new return block, that will return the result of the call.
 *
 * Switch statements, indirect branches, and exception-related terminators are
 * not currently supported.
 *
 * @param BB The BasicBlock to fixup.
 * @param ctx Context for the current BasicBlock and corresponding extracted
 *        function. This can be nullptr if the current BasicBlock has not been
 *        extracted.
 * @param bbMap A map of all extracted BasicBlocks to their contexts.
 */
void fixupTerminator(BasicBlock &BB, BBContext *ctx, BBMap &bbMap)
{
    TerminatorInst *term = BB.getTerminator();
    if (isa<ReturnInst>(term) || isa<UnreachableInst>(term)) {
        return;
    }

    if (BranchInst *branch = dyn_cast<BranchInst>(term)) {
        if (branch->isUnconditional()) {
            // handle single target branch
            BasicBlock *succ = branch->getSuccessor(0);

            IRBuilder<> builder(term);
            CallInst *callInst = createCallInst(builder, ctx, bbMap[succ]);
            builder.CreateRet(callInst);
            term->eraseFromParent();
            return;
        }
        else {
            // handle multi target branch
            BasicBlock *succ0 = branch->getSuccessor(0);
            BasicBlock *succ1 = branch->getSuccessor(1);
            BasicBlock *bb0 = BasicBlock::Create(BB.getContext(), succ0->getName(), BB.getParent());
            BasicBlock *bb1 = BasicBlock::Create(BB.getContext(), succ1->getName(), BB.getParent());
            BasicBlock *bb2 = BasicBlock::Create(BB.getContext(), "retblock", BB.getParent());

            branch->setSuccessor(0, bb0);
            branch->setSuccessor(1, bb1);

            IRBuilder <> builder(bb0);
            CallInst *callInst0 = createCallInst(builder, ctx, bbMap[succ0]);
            builder.CreateBr(bb2);

            builder.SetInsertPoint(bb1);
            CallInst *callInst1 = createCallInst(builder, ctx, bbMap[succ1]);
            builder.CreateBr(bb2);

            builder.SetInsertPoint(bb2);
            PHINode *phi = builder.CreatePHI(callInst0->getCalledFunction()->getReturnType(), 4);
            phi->addIncoming(callInst0, bb0);
            phi->addIncoming(callInst1, bb1);
            builder.CreateRet(phi);

            return;
        }
    }

    // SwitchInst, IndirectBrInst, InvokeInst, ResumeInst, CatchSwitchInst,
    // CatchReturnInst, and CleanupReturnInst are not implemented.
    errs() << "Unsupported terminator: '" << *term << "'\n";
    exit(1);
}


/**
 * @brief Replace Uses of Values with arguments. At this point, BasicBlocks
 *        still reference Values that were created outside of the current
 *        function.
 * @param ctx Context for the current extracted BasicBlock.
 */
void fixupArgumentUses(BBContext &ctx) {
    auto ai = ctx.Func->arg_begin();
    for (auto it : ctx.params) {
        Value *value = it.first;
        Argument &arg = *ai;
        arg.setName(value->getName());
        for (Use *U : it.second) {
            U->set(&arg);
        }
        ai++;
    }
}


/**
 * @brief Extract basic blocks from a function.
 * @param M Module to insert extracted functions into.
 * @param Func Function to extract BasicBlocks from.
 */
void extractBasicBlocks(Module &M, Function &Func) {
    DEBUG(dbgs() << "extractBasicBlocks(");
    DEBUG(dbgs().write_escaped(Func.getName()) << ")\n");

    // split entry block with alloca's into two blocks
    BasicBlock *startBB = &Func.getEntryBlock();
    bool containsAlloca = false;
    for (Instruction &I : *startBB) {
        if (isa<AllocaInst>(I)) {
            containsAlloca = true;
        }
        else if (containsAlloca) {
            startBB = startBB->splitBasicBlock(&I);
            break;
        }
        else {
            break;
        }
    }

    // Pass 1: Recursive postorder traversal of the CFG to determine
    // parameters needed for each extracted BasicBlock.
    BBMap bbMap;
    SmallPtrSet<BasicBlock *, 32> seenBB;
    for (int i = 0; i < 2; i++) {
        visitBasicBlock(*startBB, bbMap, seenBB);
    }

    // Pass 2: Extract BasicBlocks into new functions
    for (auto &pair : bbMap) {
        extractBasicBlock(M, *pair.second);
    }

    // Pass 3: Fixup BasicBlock transitions by converting branches to calls
    fixupTerminator(Func.getEntryBlock(), nullptr, bbMap);
    for (auto &pair : bbMap) {
        fixupTerminator(*pair.second->BB, pair.second.get(), bbMap);
        fixupArgumentUses(*pair.second);
    }
}


struct ExtractBB : public ModulePass {
    static char ID;

    ExtractBB() : ModulePass(ID) {}

    bool runOnModule(Module &M) override {
        // build the list of functions to extract before extracting them, as
        // we will be adding extracted functions to the module as we go.
        SmallVector<Function *, 32> functions;
        for (Function &Func : M) {
            // only extract BasicBlocks if the function contains more than one
            // BasicBlock. external functions will have 0 BasicBlocks.
            if (Func.size() > 1) {
                functions.push_back(&Func);
            }
        }

        for (Function *Func : functions) {
            extractBasicBlocks(M, *Func);
        }

        return false;
    }
};

static void addExtractBBPass(const PassManagerBuilder &Builder, legacy::PassManagerBase &PM) {
    PM.add(new ExtractBB());
}

}   // namespace


char ExtractBB::ID = 0;
static RegisterPass<ExtractBB> X("extractbb", "Extract Basic Blocks Pass", false, false);

// automatically register pass when loaded by clang
static RegisterStandardPasses RegisterExtractBBO0(PassManagerBuilder::EP_EnabledOnOptLevel0,
                                                  addExtractBBPass);
static RegisterStandardPasses RegisterExtractBBOx(PassManagerBuilder::EP_OptimizerLast,
                                                  addExtractBBPass);
