#ifndef __TOOLS__
#define __TOOLS__

#include "global.h"

#define PACK_BYTE 8
#define getZero(ty) Constant::getNullValue(ty)
using namespace llvm;

void make_global_array(Module& M, Type* type, unsigned size, StringRef* name, GlobalVariable* insert_before, ArrayRef<Constant*> initializer);
unsigned get_size(Type* type, Module* M);
GlobalVariable* make_global(Module& M, Type* type, Twine name, GlobalVariable* insert_before, Constant* initializer);
GlobalVariable* make_global_volatile(Module& M, Type* type, StringRef* name, GlobalVariable* insert_before, Constant* initializer);
GlobalVariable* make_global_considering_layout(Module& M, Type* type, Twine name, Constant* initializer);
bool isContainingChkpt(Function* F);
bool isMemcpy(Instruction* I);
bool isContainingCall(BasicBlock* bb);

#endif
