/*
 * This code searches for variable that is passed to a function
 * argument as a reference and promote that variable to global variable
 * if it is local one.
 * By doing so, we can do alias analysis to the vars that is passed by
 * reference
 */
#include "include/globalPromotion.h"
#include "include/tools.h"

using namespace llvm;

class GlobalPromotion : public ModulePass {
	public:
		static char ID;
		GlobalPromotion() : ModulePass(ID) { }

		virtual bool runOnModule(Module& M) {

			for (auto &F : M) {
				value_vec needPromotion;
				errs() << "F " << F.getName() << "\n";
				AliasAnalysis* AA;
				if (!F.getBasicBlockList().empty()) {
					AA = &this->getAnalysis<AAResultsWrapperPass>(F).getAAResults();
				}
				// get local variables
				value_vec local_vars;
				for (auto &B : F) {
					for (auto &I : B) {
						if (isa<AllocaInst>(&I)) {
							local_vars.push_back(&I);
							errs() << "local vars " << I.getName() << "\n";
						}
					}
				}
				for (auto &B : F) {
					for (auto &I : B) {
						if (CallInst* ci = dyn_cast<CallInst>(&I)) {
							Function* calledFunc = ci->getCalledFunction();
							if (calledFunc) {
								errs() << *ci << "\n";
								if (!calledFunc->getBasicBlockList().empty()) {
									if (isContainingChkpt(calledFunc)) {
										for (unsigned i = 0; i < ci->getNumArgOperands(); ++i) {
											Value* arg = ci->getArgOperand(i);
											if (arg->getType()->isPointerTy()) {
												errs() << "arg " << *arg << "\n";
												for (value_vec::iterator VI = local_vars.begin(), 
														VE = local_vars.end(); VI != VE; ++VI) {
													Value* pointee = NULL;
													//if (LoadInst* ld = dyn_cast<LoadInst>(arg)) {
													//	pointee = ld->getOperand(0);
													//}
													if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(arg)) {
														pointee = gep->getPointerOperand();
													}
													else if (GEPOperator* gep = dyn_cast<GEPOperator>(arg)) {
														pointee = gep->getPointerOperand();
													}
													else if (BitCastInst* bc = dyn_cast<BitCastInst>(arg)) {
														pointee = bc->getOperand(0);
													}
													else if (arg->getType()->isPointerTy()) {
														// if it is struct, somehow it works as a pointer
														pointee = arg;
													}
													assert(pointee);
													AliasResult aresult = AA->alias(pointee, *VI);
													// TODO: passing the ref is what we need to detect!
													// CURRENTLY WE ARE DOING WRONG THING
													if (aresult != AliasResult::NoAlias) {
														errs() << "this needs promotion " << *(*VI) << "\n";
														if (!isAlreadyIn(needPromotion, *VI))
															needPromotion.push_back(*VI);
													}
												}
											}
										}
									}
								}
							}
						}
					}
				}
				
				// promote to global
				for (value_vec::iterator VI = needPromotion.begin(), VE = needPromotion.end();
						VI != VE; ++VI) {
					// TODO: Do not need to make in NV!!
					GlobalVariable* gv = make_global_volatile(M, (*VI)->getType()->getContainedType(0), 
							new StringRef((*VI)->getName().str() + "_promoted_" + F.getName().str()), 
							NULL, getZero((*VI)->getType()->getContainedType(0)));
					errs() << "replace " << *gv << " with " << *(*VI) << "\n";
					(*VI)->replaceAllUsesWith(gv);
					// TODO: this sometimes does not work nicely..
					Instruction* alloca = cast<Instruction>(*VI);
					alloca->eraseFromParent();
				}
			}
			return true;
		}

		virtual void getAnalysisUsage(AnalysisUsage& AU) const {
			AU.setPreservesAll();
			AU.addRequired<AAResultsWrapperPass>();
		}

	private:
};
char GlobalPromotion::ID = 1;
//char* taskAnalysisID = &TaskAnalysis::ID;
RegisterPass<GlobalPromotion> GP("globalpromotion", "Global-Promotion");
