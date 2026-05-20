```cpp
#include "llvm/Transforms/Obfuscation/Flattening.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include <algorithm>
#include <cstdlib>
#include <vector>
using namespace llvm;
namespace polaris {

Function *Flattening::buildUpdateKeyFunc(Module *m) {
  std::vector<Type *> params;
  params.push_back(Type::getInt8Ty(m->getContext()));
  params.push_back(Type::getInt32Ty(m->getContext()));
  params.push_back(Type::getInt32Ty(m->getContext())->getPointerTo());
  params.push_back(Type::getInt32Ty(m->getContext())->getPointerTo());
  params.push_back(Type::getInt32Ty(m->getContext()));
  FunctionType *funcType =
      FunctionType::get(Type::getVoidTy(m->getContext()), params, false);
  Function *func = Function::Create(funcType, GlobalValue::PrivateLinkage,
                                    Twine("ollvm"), m);
  BasicBlock *entry = BasicBlock::Create(m->getContext(), "entry", func);
  BasicBlock *cond = BasicBlock::Create(m->getContext(), "cond", func);
  BasicBlock *update = BasicBlock::Create(m->getContext(), "update", func);
  BasicBlock *end = BasicBlock::Create(m->getContext(), "end", func);
  Function::arg_iterator iter = func->arg_begin();
  Value *flag = iter;
  Value *len = ++iter;
  Value *posArray = ++iter;
  Value *keyArray = ++iter;
  Value *num = ++iter;
  IRBuilder<> irb(entry);
  Value *i = irb.CreateAlloca(irb.getInt32Ty());
  irb.CreateStore(irb.getInt32(0), i);
  irb.CreateCondBr(irb.CreateICmpEQ(flag, irb.getInt8(0)), cond, end);

  irb.SetInsertPoint(cond);
  irb.CreateCondBr(irb.CreateICmpSLT(irb.CreateLoad(irb.getInt32Ty(), i), len),
                   update, end);

  irb.SetInsertPoint(update);

  Value *pos = irb.CreateLoad(
      irb.getInt32Ty(), irb.CreateGEP(irb.getInt32Ty(), posArray,
                                      irb.CreateLoad(irb.getInt32Ty(), i)));
  Value *key = irb.CreateGEP(irb.getInt32Ty(), keyArray, pos);
  irb.CreateStore(irb.CreateXor(irb.CreateLoad(irb.getInt32Ty(), key), num),
                  key);
  irb.CreateStore(
      irb.CreateAdd(irb.CreateLoad(irb.getInt32Ty(), i), irb.getInt32(1)), i);
  irb.CreateBr(cond);

  irb.SetInsertPoint(end);
  irb.CreateRetVoid();
  return func;
}

void Flattening::doFlatten(Function *f, int seed, Function *updateFunc) {
  // ==================== 修复：跳过包含内联汇编的函数 ====================
  // 含有 asm("backend-obfu") 的函数会导致 SelectInst::init 崩溃
  // 直接跳过，避免平坦化
  for (BasicBlock &BB : *f) {
    for (Instruction &I : BB) {
      if (CallBase *CB = dyn_cast<CallBase>(&I)) {
        if (CB->isInlineAsm()) {
          errs() << "FLA: Skip function " << f->getName() << " (contains inline asm)\n";
          return;  // 提前退出，不做平坦化
        }
      }
    }
  }
  // ====================================================================

  srand(seed);
  std::vector<BasicBlock *> origBB;
  for (BasicBlock &basicBlock : *f)
    origBB.push_back(&basicBlock);
  if (origBB.size() <= 1)
    return;
  unsigned int rand_val = seed;
  Function::iterator tmp = f->begin();
  BasicBlock *oldEntry = &*tmp;
  origBB.erase(origBB.begin());
  BranchInst *firstBr = NULL;
  if (isa<BranchInst>(oldEntry->getTerminator()))
    firstBr = cast<BranchInst>(oldEntry->getTerminator());
  BasicBlock *firstbb = oldEntry->getTerminator()->getSuccessor(0);
  if ((firstBr != NULL && firstBr->isConditional()) ||
      oldEntry->getTerminator()->getNumSuccessors() >
          2) // Split the first basic block
  {
    BasicBlock::iterator iter = oldEntry->end();
    iter--;
    if (oldEntry->size() > 1)
      iter--;
    BasicBlock *splited = oldEntry->splitBasicBlock(iter, Twine("FirstBB"));
    firstbb = splited;
    origBB.insert(origBB.begin(), splited);
  }
  BasicBlock *newEntry = oldEntry; // Prepare basic block
  BasicBlock *loopBegin =
      BasicBlock::Create(f->getContext(), "LoopBegin", f, newEntry);
  BasicBlock *defaultCase =
      BasicBlock::Create(f->getContext(), "DefaultCase", f, newEntry);
  BasicBlock *loopEnd =
      BasicBlock::Create(f->getContext(), "LoopEnd", f, newEntry);
  newEntry->moveBefore(loopBegin);
  BranchInst::Create(
      loopEnd, defaultCase); // Create branch instruction,link basic blocks
  BranchInst::Create(loopBegin, loopEnd);
  newEntry->getTerminator()->eraseFromParent();
  BranchInst::Create(loopBegin, newEntry);
  AllocaInst *switchVar =
      new AllocaInst(Type::getInt32Ty(f->getContext()), 0, Twine("switchVar"),
                     newEntry->getTerminator()); // Create switch variable
  LoadInst *value =
      new LoadInst(switchVar->getAllocatedType(), switchVar, "cmd", loopBegin);
  SwitchInst *sw = SwitchInst::Create(value, defaultCase, 0, loopBegin);
  std::vector<unsigned int> rand_list;
  unsigned int startNum = 0;
  for (std::vector<BasicBlock *>::iterator b = origBB.begin();
       b != origBB.end(); b++) // Put basic blocks into switch structure
  {
    BasicBlock *block = *b;
    block->moveBefore(loopEnd);
    unsigned int num = getUniqueNumber(rand_list);
    rand_list.push_back(num);
    if (block == firstbb)
      startNum = num;
    ConstantInt *numCase =
        cast<ConstantInt>(ConstantInt::get(sw->getCondition()->getType(), num));
    sw->addCase(numCase, block);
  }
  ConstantInt *startVal = cast<ConstantInt>(ConstantInt::get(
      sw->getCondition()->getType(), startNum)); // Set the entry value
  new StoreInst(startVal, switchVar, newEntry->getTerminator());
  errs() << "Put Block Into Switch\n";
  for (std::vector<BasicBlock *>::iterator b = origBB.begin();
       b != origBB.end(); b++) // Handle successors
  {
    BasicBlock *block = *b;
    if (block->getTerminator()->getNumSuccessors() == 1) {
      errs() << "This block has 1 successor\n";
      BasicBlock *succ = block->getTerminator()->getSuccessor(0);
      ConstantInt *caseNum = sw->findCaseDest(succ);
      if (caseNum == NULL) {
        unsigned int num = getUniqueNumber(rand_list);
        rand_list.push_back(num);
        caseNum = cast<ConstantInt>(
            ConstantInt::get(sw->getCondition()->getType(), num));
      }
      block->getTerminator()->eraseFromParent();
      new StoreInst(caseNum, switchVar, block);
      BranchInst::Create(loopEnd, block);
    } else if (block->getTerminator()->getNumSuccessors() == 2) {
      errs() << "This block has 2 successors\n";
      BasicBlock *succTrue = block->getTerminator()->getSuccessor(0);
      BasicBlock *succFalse = block->getTerminator()->getSuccessor(1);
      ConstantInt *numTrue = sw->findCaseDest(succTrue);
      ConstantInt *numFalse = sw->findCaseDest(succFalse);
      if (numTrue == NULL) {
        unsigned int num = getUniqueNumber(rand_list);
        rand_list.push_back(num);
        numTrue = cast<ConstantInt>(
            ConstantInt::get(sw->getCondition()->getType(), num));
      }
      if (numFalse == NULL) {
        unsigned int num = getUniqueNumber(rand_list);
        rand_list.push_back(num);
        numFalse = cast<ConstantInt>(
            ConstantInt::get(sw->getCondition()->getType(), num));
      }
      BranchInst *oldBr = cast<BranchInst>(block->getTerminator());
      SelectInst *select =
          SelectInst::Create(oldBr->getCondition(), numTrue, numFalse,
                             Twine("choice"), block->getTerminator());
      block->getTerminator()->eraseFromParent();
      new StoreInst(select, switchVar, block);
      BranchInst::Create(loopEnd, block);
    } else
      continue;
  }
  demoteRegisters(f);
}

PreservedAnalyses Flattening::run(Module &M, ModuleAnalysisManager &AM) {
  Function *updateFunc = buildUpdateKeyFunc(&M);
  for (Function &f : M) {
    if (&f == updateFunc)
      continue;
    if (readAnnotate(f).find("flatten") != std::string::npos) {
      doFlatten(&f, 0, updateFunc);
    }
  }

  return PreservedAnalyses::none();
}
} // namespace polaris
```
