#ifndef __LIVEVARANAL__
#define __LIVEVARANAL__

#include "analyzeTool.h"
#include "global.h"
#include "dataflow.h"

using namespace llvm;

extern std::vector<Value*>* lva_vals;
extern Pass* callerPass;
extern std::map<Function*, Analysis*>* lva_liveVarResults;

void analyzeLiveVar(Module& M);
void findAllVars(Module& M);
void gen(Instruction *I, BitVector* gen_set);
void kill(Instruction *I, BitVector* result);
BitVector* func(Instruction* I, BitVector* input);
value_vec analyzeConstant(Module& M);
value_vec analyzeConstLocalVar(Module& M);

#endif
