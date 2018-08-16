#include "include/analysis.h"

using namespace llvm;

class GetLoopCount : public ModulePass {
	public:
		std::ofstream log;
		std::ofstream log2;
		static char ID;

		GetLoopCount() : ModulePass(ID) { }
		std::vector<BasicBlock*> lr_stack;
		void saveLoopCount(Module& M, BasicBlock& block){
			//errs() << "traversing.. " << block << "\n";
			///
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(*(block.getParent())).getLoopInfo();	
			///
			if(LI.getLoopFor(&block)){
				//ScalarEvolution &SEWP = getAnalysis<ScalarEvolutionWrapperPass>(*(LI.getLoopFor(&block))).getSE();	
				ScalarEvolution &SEWP = getAnalysis<ScalarEvolutionWrapperPass>(*(block.getParent())).getSE();	
				unsigned loopcount = SEWP.getSmallConstantTripCount(LI.getLoopFor(&block));
				if (loopcount == 0) {
					log2 << 0 << "\n"; // loop is not simple
					for (BasicBlock::iterator i = block.begin(), e = block.end(); i!=e; ++i) {
						Instruction *I = i;
						if (CallInst* ci = dyn_cast<CallInst>(I)) {
							if (ci->getCalledFunction() != NULL) {
								if (ci->getCalledFunction()->getName().str().find("__loop_bound") != std::string::npos) {
									loopcount = cast<ConstantInt>(ci->getArgOperand(0))->getZExtValue();
									// we need to get rid of __loop_bound__
								}
							}
						}
					}
				}
				else {
					log2 << 1 << "\n"; // loop is simple
				}
				//outs() << &block << "\n";
				//outs() << "loop! " << loopcount << "\n";
				log << loopcount << "\n";
			}
			else{
				//outs() << "no loop!\n";
			}
			visitedBb.push_back(&block);
			Node* cur_node;
			Edge* edge;
			for (BasicBlock::iterator i = block.begin(), e = block.end(); i!=e; ++i) {
				Instruction *I = i;
			}
#if 0
			// if it is return (Not main but no successor)
			if (succ_begin(&block) == succ_end(&block) && block.getParent()->getName().str().find("main") == std::string::npos) {
				if (!isa<ReturnInst>(block.getTerminator())) {
					// program exit (ex - exit(0)). Do nothing
				}
				else {
					assert(lr_stack.size() != 0);
					BasicBlock* succ = lr_stack.back();
					lr_stack.pop_back();

					// when succ is never visited
					if (std::find(visitedBb.begin(), visitedBb.end(), succ) == visitedBb.end()){
						saveLoopCount(M, *succ);
					}
				}
			}
#endif
			// to successor blocks
			for(succ_iterator SI = succ_begin(&block); SI != succ_end(&block); ++SI){
				BasicBlock* succ = *SI;
#if 0
				if (!(succ->hasName()) && !(succ_begin(succ)->hasName())) {
					CallInst* callInst = dyn_cast<CallInst>(&(succ->front()));
					assert(callInst != NULL);
					BasicBlock* newSucc = &(callInst->getCalledFunction()->front()); 

					// when succ is never visited
					if (std::find(visitedBb.begin(), visitedBb.end(), newSucc) == visitedBb.end()){
						// and it must have single successor
						BasicBlock* succBB = *(succ_begin(succ));
						lr_stack.push_back(succBB);
						saveLoopCount(M, *newSucc);
					}
					else {
						BasicBlock* succBB = *(succ_begin(succ));
						saveLoopCount(M, *succBB);
					}
				}
				else { 
#endif
					if(std::find(visitedBb.begin(), visitedBb.end(), succ) == visitedBb.end()){
						saveLoopCount(M, *succ);
					}
//				}
			}
		}

		virtual bool runOnModule(Module& M) {
			Function* main = M.getFunction("main");
			log.open("./loopcount.log");
			log2.open("./loopsimplicity.log");
			for (auto &F : M) {
				// do not analyze external functions
				if (!F.getBasicBlockList().empty()) {
//					saveLoopCount(M, main->getEntryBlock());
					saveLoopCount(M, F.getEntryBlock());
				}
			}
			log.close();
			log2.close();
			return false;
		}

		virtual void getAnalysisUsage(AnalysisUsage& AU) const {
			AU.setPreservesAll();
			AU.addRequired<LoopInfoWrapperPass>();
			AU.addRequired<ScalarEvolutionWrapperPass>();
		}

	private:
};
char GetLoopCount::ID = 2;
RegisterPass<GetLoopCount> Z("getloopcount", "15745 Liveness");
