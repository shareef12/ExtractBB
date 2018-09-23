/**
 * @brief Module pass to extract instructions into functions.
 *
 * This pass will individually process each function, extracting instructions
 * into new functions. Edges between instructions and basic blocks will be
 * converted into calls. As a side-effect of this, loops will be translated
 * into recursive calls.
 *
 * At the moment, the only supported Terminator instructions for BasicBlocks
 * are returns and branches. The following terminators are not implemented:
 *  - switch statements
 *  - indirect branches
 *  - exceptions/cleanup
 */

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
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

STATISTIC(NumBlocksExtracted, "Number of basic blocks extracted");

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
 * @member phis A map of incoming PHINodes for this basic block. Each PHINode
 *         will become an additional parameter. They need to be tracked
 *         separately from params because they need special handling and will
 *         be removed once we're done processing all BasicBlocks.
 */
struct BBContext {
    BasicBlock *BB;
    Function *Func;
    std::map<Value *, SmallVector<Use *, 4>> params;
    std::map<PHINode *, SmallVector<Use *, 2>> phis;
};

typedef std::map<BasicBlock *, std::unique_ptr<BBContext>> BBMap;


/**
 * @brief Split a BasicBlock after the first insertion point.
 * @param BB BasicBlock to split.
 */
void splitBasicBlock(BasicBlock &BB) {
    auto it = BB.getFirstInsertionPt();
    if (it == BB.end() || std::next(it) == BB.end()) {
        return;
    }
    BB.splitBasicBlock(std::next(it));
}


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

        // PHINodes need special handling. In this case, we have two input
        // values, but only need one parameter. Add the PHI to the context with
        // no uses (it will be erased later). We also have to iterate through
        // the PHINode Users in the current block to properly replace it's
        // Uses.
        if (PHINode *phi = dyn_cast<PHINode>(&I)) {
            ctx->phis[phi] = std::move(SmallVector<Use *, 4>());
            continue;
        }

        for (Use &U : I.operands()) {
            Value *value = U.get();

            // globals and constants don't need to become parameters.
            // llvm GlobalValue subclasses llvm::Constant.
            if (isa<Constant>(value)) {
                continue;
            }

            // Uses of Values that aren't Instructions or Arguments
            // (BasicBlocks by a BranchInst, Functions by a CallInst), don't
            // require a parameter.
            if (!isa<Instruction>(value) && !isa<Argument>(value)) {
                continue;
            }

            // Unless it's PHINode, Values from the current BasicBlock don't
            // need to become parameters.
            if (auto *VI = dyn_cast<Instruction>(value)) {
                if (!isa<PHINode>(value) && VI->getParent() == &BB) {
                    continue;
                }
            }

            DEBUG(dbgs() << "      ");
            DEBUG(value->dump());

            // PHINode in the current BasicBlock is tracked separately
            if (PHINode *phi = dyn_cast<PHINode>(value)) {
                if (phi->getParent() == &BB) {
                    ctx->phis[phi].push_back(&U);
                    continue;
                }
            }

            // normal parameter - add it to the param list
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

        // add succ params to this function params if they aren't produced in
        // this BasicBlock. succ params won't have any Uses associated with
        // them since there is no CallInst yet.
        BBContext *succCtx = bbMap[*si].get();
        for (auto &it : succCtx->params) {
            Value *value = it.first;
            if (Instruction *I = dyn_cast<Instruction>(value)) {
                if (I->getParent() == &BB) {
                    continue;
                }
            }

            if (ctx->params.count(value) == 0) {
                ctx->params[value] = std::move(SmallVector<Use *, 4>());
            }
        }

        // if the succ has PHINodes that depend on a Value produced by one of
        // our parent BasicBlocks, that Value needs to become a parameter.
        for (auto &it : succCtx->phis) {
            PHINode *phi = it.first;
            Value *value = phi->getIncomingValueForBlock(&BB);
            if (Instruction *I = dyn_cast<Instruction>(value)) {
                if (I->getParent() == &BB) {
                    continue;
                }
            }

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
    for (auto &it : ctx.params) {
        Value *value = it.first;
        argsTy.push_back(value->getType());
    }
    for (auto &it : ctx.phis) {
        PHINode *phi = it.first;
        argsTy.push_back(phi->getType());
    }

    Type *retTy = ctx.BB->getParent()->getReturnType();
    FunctionType *funcTy = FunctionType::get(retTy, argsTy, false);
    Twine funcName = ctx.BB->getParent()->getName() + "_extracted_" + ctx.BB->getName();
    ctx.Func = Function::Create(funcTy, GlobalValue::InternalLinkage, funcName, &M);

    // move the basic block to the new function
    ctx.BB->removeFromParent();
    ctx.BB->insertInto(ctx.Func);
}


/**
 * @brief Helper function to create a CallInst to an extracted BasicBlock.
 * @param BB Original BasicBlock that is being modified.
 * @param builder IRBuilder that should be used to insert instructions.
 * @param ctx Context for the current extracted function. This can be nullptr
 *        if the current function is not an extracted BasicBlock.
 * @param targetCtx Context representing the extracted BasicBlock that should
 *        be used as the call target.
 */
CallInst * createCallInst(BasicBlock &BB, IRBuilder<> &builder, BBContext *ctx,
                          BBContext &targetCtx) {
    // build argument array for the call from the child
    SmallVector<Value *, 8> args;
    for (auto &it : targetCtx.params) {
        Value *value = it.first;
        args.push_back(value);
    }
    for (auto &it : targetCtx.phis) {
        PHINode *phi = it.first;
        Value *arg = phi->getIncomingValueForBlock(&BB);
        args.push_back(arg);
    }

    CallInst *callInst = builder.CreateCall(targetCtx.Func, args);

    // if this BasicBlock was extracted, add the new uses to the list
    // of uses for the arguments so it can be properly replaced later.
    if (ctx != nullptr) {
        for (Use &U : callInst->arg_operands()) {
            Value *value = U.get();
            if (ctx->params.count(value) > 0) {
                ctx->params[value].push_back(&U);
            }
            else if (PHINode *phi = dyn_cast<PHINode>(value)) {
                if (ctx->phis.count(phi) > 0) {
                    ctx->phis[phi].push_back(&U);
                }
            }
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
            CallInst *callInst = createCallInst(BB, builder, ctx, *bbMap[succ]);
            builder.CreateRet(callInst);
            term->eraseFromParent();
            return;
        }
        else {
            // handle multi target branch
            BasicBlock *succ0 = branch->getSuccessor(0);
            BasicBlock *succ1 = branch->getSuccessor(1);
            BasicBlock *bb0 = BasicBlock::Create(BB.getContext(), "call_" + succ0->getName(),
                                                 BB.getParent());
            BasicBlock *bb1 = BasicBlock::Create(BB.getContext(), "call_" + succ1->getName(),
                                                 BB.getParent());
            BasicBlock *bb2 = BasicBlock::Create(BB.getContext(), "retblock", BB.getParent());

            branch->setSuccessor(0, bb0);
            branch->setSuccessor(1, bb1);

            IRBuilder <> builder(bb0);
            CallInst *callInst0 = createCallInst(BB, builder, ctx, *bbMap[succ0]);
            builder.CreateBr(bb2);

            builder.SetInsertPoint(bb1);
            CallInst *callInst1 = createCallInst(BB, builder, ctx, *bbMap[succ1]);
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
    for (auto &it : ctx.params) {
        Value *value = it.first;
        Argument &arg = *ai;
        arg.setName(value->getName());
        for (Use *U : it.second) {
            U->set(&arg);
        }
        ai++;
    }
    for (auto &it : ctx.phis) {
        PHINode *phi = it.first;
        Argument &arg = *ai;
        arg.setName(phi->getName());
        for (Use *U : it.second) {
            U->set(&arg);
        }
        ai++;
    }
}


/**
 * @brief Remove PHINodes that were replaced with parameters.
 * @param ctx Context for the current extracted BasicBlock.
 */
void removePhis(BBContext &ctx) {
    for (auto &it : ctx.phis) {
        PHINode *phi = it.first;
        phi->eraseFromParent();
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

    // add a dummy BasicBlock as the function entry block that only branches
    // to the true entry block. this will ensure we have a single BasicBlock
    // that will be the root node for the postorder traversal.
    BasicBlock &startBB = Func.getEntryBlock();
    BasicBlock *entryBB = BasicBlock::Create(Func.getContext(), "entry", &Func, &startBB);
    IRBuilder<> builder(entryBB);
    builder.CreateBr(&startBB);

    // Pass 1: Split BasicBlocks into blocks with a single Instruction
    for (BasicBlock &BB : Func) {
        splitBasicBlock(BB);
    }

    // Pass 2: Recursive postorder traversal of the CFG to determine
    // parameters needed for each extracted BasicBlock. Two iterations are
    // required to handle loops.
    BBMap bbMap;
    SmallPtrSet<BasicBlock *, 32> seenBB;
    for (int i = 0; i < 2; i++) {
        visitBasicBlock(startBB, bbMap, seenBB);
    }

    // Pass 3: Extract BasicBlocks into new functions
    for (auto &pair : bbMap) {
        extractBasicBlock(M, *pair.second);
    }

    // Pass 4: Fixup BasicBlock transitions by converting branches to calls
    fixupTerminator(*entryBB, nullptr, bbMap);
    for (auto &pair : bbMap) {
        fixupTerminator(*pair.second->BB, pair.second.get(), bbMap);
        fixupArgumentUses(*pair.second);
    }


    // Pass 5: Remove PHINodes that were replaced with parameters
    for (auto &pair : bbMap) {
        removePhis(*pair.second);
    }

    NumBlocksExtracted += bbMap.size();
}


struct ExtractBB : public ModulePass {
    static char ID;

    ExtractBB() : ModulePass(ID) {}

    bool runOnModule(Module &M) override {
        // build the list of functions to extract before extracting them, as
        // we will be adding extracted functions to the module as we go.
        SmallVector<Function *, 32> functions;
        for (Function &Func : M) {
            // only extract BasicBlocks if the function contains at least one
            // BasicBlock. external functions will have 0 BasicBlocks.
            if (!Func.empty()) {
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
static RegisterPass<ExtractBB> X("extractbb", "Extract Basic Blocks", false, false);

// automatically register pass when loaded by clang
static RegisterStandardPasses RegisterExtractBBO0(PassManagerBuilder::EP_EnabledOnOptLevel0,
                                                  addExtractBBPass);
static RegisterStandardPasses RegisterExtractBBOx(PassManagerBuilder::EP_OptimizerLast,
                                                  addExtractBBPass);
