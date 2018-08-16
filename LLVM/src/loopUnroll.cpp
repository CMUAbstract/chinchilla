#include "include/analysis.h"

using namespace llvm;

class LoopUnroll : public ModulePass {
	public:
		LoopUnroll() : ModulePass(ID) { }
		virtual bool runOnModule(Module& M) {
			std::vector<unsigned> loop_count_vec;
			eraseAnnotation(M);
			readLoopCount(&loop_count_vec);
		}
