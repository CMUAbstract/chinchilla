#ifndef __GLOBAL__
#define __GLOBAL__

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include <string>
#include "llvm/IR/CFG.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include <fstream>
#include <iostream>
#include <time.h>
#include <stdlib.h>
#include "llvm/IR/Attributes.h"
#include <map>
#include <set>
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/PassSupport.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Instructions.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/CFG.h"

typedef std::vector<llvm::Value*> value_vec;
typedef std::vector<llvm::GlobalVariable*> gv_vec;
typedef std::vector<llvm::Instruction*> inst_vec;
typedef struct _gv_alloc_ll {
	llvm::GlobalVariable* gvar;
	unsigned size;
	unsigned accum_size;
	struct _gv_alloc_ll* next;
	struct _gv_alloc_ll* prev;
	bool is_pack_begin;
} gv_alloc_ll;
extern gv_alloc_ll* ll_head;

#define isAlreadyIn(vec, val) (std::find(vec.begin(), vec.end(), val) != vec.end())

#endif
