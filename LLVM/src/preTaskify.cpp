#include "include/preTaskify.h"
using namespace llvm;

class PreTaskify : public ModulePass {
	public:
		static char ID;
		PreTaskify() : ModulePass(ID) { }
		void powerfulReplace(Instruction* I, Value* oldVal, Value* newVal) {
			for (unsigned i = 0; i < I->getNumOperands(); ++i) {
				// error handling for GEPOperator
				//				if(GEPOperator* gep = dyn_cast<GEPOperator>(I->getOperand(i))){
				//					errs() << "gep! " << *I << "\n";
				//					Value* gepVal = gep->getPointerOperand();
				//					if (oldVal == gepVal) {
				//						// switch it
				//						std::vector<Value*> arrayRef;
				//						for (llvm::User::op_iterator uit = gep->idx_begin(), ue = gep->idx_end(); uit != ue; ++uit){
				//							arrayRef.push_back(uit->get());
				//						}
				//						GetElementPtrInst* gep_new = llvm::GetElementPtrInst::CreateInBounds(newVal, ArrayRef<Value*>(arrayRef), "", I);
				//						gep_new->insertBefore(I);
				//						//						gep_new->setPointerOperand(newVal);
				//						assert(newVal != (Value*)0x1);
				//						I->setOperand(i, gep_new);
				//					}
				//
				//				}
				//				else {
				if (I->getOperand(i) == oldVal) {
					assert(newVal != (Value*)0x1);
					// switch it
					if (isa<GlobalVariable>(newVal)) {
						LoadInst* li = new LoadInst(newVal, "", I);
						I->setOperand(i, li);
					}
					else {
						I->setOperand(i, newVal);
					}
				}
				//				}
			}
		}
		void preTaskify(Function* F) {
#if 0
			// 1. make each argument global : no worry about reusing. No function is recursive
			std::map<unsigned, GlobalVariable*> arg_map; // map to save arg - global pair
			unsigned arg_count = 0;
			for (Function::arg_iterator ait = F->arg_begin(), ae = F->arg_end(); ait != ae; ++ait, ++arg_count) {
				// declare new global
				Constant* zero = Constant::getNullValue(ait->getType());
				GlobalVariable* arg_gb = new GlobalVariable(*(F->getParent()), (ait)->getType(), false, GlobalValue::ExternalLinkage, zero, F->getName() + "_" + (ait)->getName());
				arg_gb->setAlignment(2);
				arg_map[arg_count] = arg_gb;
			}
			// 1.5 make ret_task as global
//			Constant* zero_ptr = Constant::getNullValue(Type::getInt8PtrTy(F->getContext()));
//			GlobalVariable* ret_task = new GlobalVariable(*(F->getParent()), Type::getInt8PtrTy(F->getContext()), false, GlobalValue::ExternalLinkage, zero_ptr, F->getName() + "_ret_task");
//			ret_task->setAlignment(2);
//			arg_map[arg_count] = arg_gb;
			Constant* zero_ptr = Constant::getNullValue(Type::getInt8PtrTy(F->getContext()));
			GlobalVariable* ret_task = new GlobalVariable(*(F->getParent()), Type::getInt8PtrTy(F->getContext()), false, GlobalValue::ExternalLinkage, zero_ptr, "_global_" + F->getName() + "_ret_task");
			ret_task->setSection(".nv_vars");
			ret_task->setAlignment(2);


			// cut bb where it calls the function
			for (Value::user_iterator uit = F->user_begin(), ue = F->user_end(); uit != ue; ++uit) {
				// find the call point
				CallInst* callInst = dyn_cast<CallInst>(*uit);
				if (callInst != NULL) {
					// cut the basicblock into two (because call and return will be TRANSITION_TO)
					BasicBlock::iterator bit = BasicBlock::iterator(callInst);
					bit++; // get the next instruction
					Instruction* next_inst = dyn_cast<Instruction>(bit);
				//	callInst->getParent()->splitBasicBlock(next_inst);
					BasicBlock* beforeCall = callInst->getParent();
					callInst->getParent()->splitBasicBlock(callInst); // cut before callInst
					callInst->getParent()->splitBasicBlock(next_inst); // cut after callInst

					// pass arguments explicitly

					// 2. before call inst, insert store to the global_arg
					for (unsigned i = 0; i < arg_map.size(); ++i) {
						StoreInst* st = new StoreInst(callInst->getArgOperand(i), arg_map[i], beforeCall->getTerminator());
					}
					// 2.5 save ret_task
				}
			}

			// 3. in the function, replace every use of arg to global_arg
			// 4. same for return..
			for (auto &B : *F) {
				for (auto &I : B) {
					if (!isa<ReturnInst>(&I)) {
						arg_count = 0;
						for (Function::arg_iterator ait = F->arg_begin(), ae = F->arg_end(); ait != ae; ++ait, ++arg_count) {
							powerfulReplace(&I, ait, arg_map[arg_count]);
						}
					}
					else {
						ReturnInst* reti = dyn_cast<ReturnInst>(&I);
						if (reti->getNumOperands() == 0) { // void return
						}
						else {
							assert(reti->getNumOperands() == 1); // can it be  > 2?
							// save retval to global
							Constant* zero = Constant::getNullValue(reti->getOperand(0)->getType());
							GlobalVariable* ret_gb = new GlobalVariable(*(F->getParent()), reti->getOperand(0)->getType(), false, GlobalValue::ExternalLinkage, zero, F->getName() + "_ret");
							ret_gb->setAlignment(2);
							StoreInst* st = new StoreInst(reti->getOperand(0), ret_gb, reti);

							// if any instruction in the mother function uses return val, switch it to proper val as well
							for (Value::user_iterator uit = F->user_begin(), ue = F->user_end(); uit != ue; ++uit) {
								// find the call point
								CallInst* callInst = dyn_cast<CallInst>(*uit);
								if (callInst != NULL) {
									for (auto &B : *(callInst->getParent()->getParent())) {
										for (auto &I : B) {
											for (unsigned i = 0; i < I.getNumOperands(); ++i) {
												powerfulReplace(&I, callInst, ret_gb);
											}
										}
									}
								}
							}
						}
					}
				}
			}

			// 5. then, move the entire function bbs into main.
			// 6. and pad call with branch
			// 7. and return with branch back
			// But these three step has to be executed after inlining > customInliningPost.cpp
#endif
			// cut bb where it calls the function
			for (Value::user_iterator uit = F->user_begin(), ue = F->user_end(); uit != ue; ++uit) {
				// find the call point
				CallInst* callInst = dyn_cast<CallInst>(*uit);
				if (callInst != NULL) {
					// cut the basicblock into two 
					BasicBlock* beforeCall = callInst->getParent();
					callInst->getParent()->splitBasicBlock(callInst); // cut before callInst
					BasicBlock::iterator bit = BasicBlock::iterator(callInst);
					bit++; // get the next instruction
					Instruction* next_inst = dyn_cast<Instruction>(bit);
				//	callInst->getParent()->splitBasicBlock(next_inst);
					callInst->getParent()->splitBasicBlock(next_inst); // cut after callInst
				}
			}
		}
		virtual bool runOnModule(Module& M) {
			std::vector<Function*> eraseVec;
			for (auto &F : M) {
				if (!F.getBasicBlockList().empty()) {
					if (F.getName().str() != "main" &&
							F.getName().str() != "init_hw" &&
							// maybe this is unnecessary
							F.getName().str() != "__loop_bound__" &&
							F.getName().str() != "TimerB1_ISR" &&
							F.getName().str() != "init") {
						errs() << "F: " << F.getName() << "\n";
						preTaskify(&F);		
					}
				}
			}

			// Did not modify the incoming Function.
			return true;
		}

		virtual void getAnalysisUsage(AnalysisUsage& AU) const {
			AU.setPreservesAll();
		}

	private:
};
char PreTaskify::ID = 1;
//char* taskAnalysisID = &TaskAnalysis::ID;
RegisterPass<PreTaskify> PT("pretaskify", "Pre-Taskify");
