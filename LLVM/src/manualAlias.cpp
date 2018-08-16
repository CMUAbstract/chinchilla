#include "include/manualAlias.h"

/*
 * This function searches some definite alias that
 * LLVM misses for default
 */
unsigned manualAlias(Value* v1, Value* v2, Instruction* I) {
	// Usually, the ones that LLVM miss but is obvious to us is
	// the GEPs. Actually nothing is guaranteed,
	// (e.g., A[100000] can point to anything)
	// But we assume it is not the case and do some aggressive
	// guessing.
	if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(I)) {

		
	}
	else {
		return AliasResult::MayAlias;
	}
}
