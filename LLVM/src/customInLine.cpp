#include "include/customInLine.h"
using namespace llvm;

#define NOINLINE_NUM 0 // TODO: This has to come from script argument: TEMP: 999 is never inline
class CustomInLine : public ModulePass {
	public:
		static char ID;
		CustomInLine() : ModulePass(ID) { }
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
		unsigned getCalledTime(Function* F) {
			if (F->getName().str().find("main") != std::string::npos) {
				return 1;
			}
			unsigned count = 0;
			for (Value::user_iterator uit = F->user_begin(), ue = F->user_end(); uit != ue; ++uit) {
				// This won't handle function pointer + call using pointer
				// However those won't get inlined anyway.
				// TODO: If that happens, can the system even handle that?
				CallInst* callInst = dyn_cast<CallInst>(*uit);

				if (callInst != NULL) {
					Function* caller = callInst->getParent()->getParent();
					count += getCalledTime(caller);
				}
			}

			return count;
		}
		struct func_cmp {
			bool operator ()(const std::pair<Function*, unsigned> &a, const std::pair<Function*, unsigned> &b) {
				return a.second > b.second;
			}
		};
		void preTaskify(Function* F) {
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
		}
		virtual bool runOnModule(Module& M) {
			//std::set<std::pair<Function*, unsigned>, func_cmp> func_set;
			std::vector<std::pair<Function*, unsigned>> func_vec;
			// this tot line number should not exceed certain value
			for (auto &F : M) {
				unsigned curFuncLine = 0; // this indicate how much code will this function add (w or w/o inlining)
				// for each function (including main)
				for (auto &B : F) {
					for (auto &I : B) {
						++curFuncLine; // count line num
					}
				}

				unsigned calledTime = getCalledTime(&F);
				curFuncLine *= calledTime;
				// TODO: this has to be calledTime - 1 because we care about the delta
				errs() << F.getName() << " is called " << calledTime << " times!\nLine added: " << curFuncLine << "\n";

				if (curFuncLine > 0) {
					func_vec.push_back(std::make_pair(&F, curFuncLine));
					errs() << "func num: " << func_vec.size() << "\n";
				}
				// TODO: the rule I am proposing is first try compiling and only if there is ROM overflow
				// try to not inline some of the function by recompilation script.
			}

			// Sort in ascending order
			unsigned noInline_counter = 0;
			while (func_vec.size() != 0) {
				//			for (std::set<std::pair<Function*, unsigned>, func_cmp>::iterator sit = func_set.begin(), se = func_set.end(); sit != se; ++sit) {
				unsigned highest = 0;
				unsigned highest_index = 0;
				unsigned i = 0;
				for (std::vector<std::pair<Function*, unsigned>>::iterator fit = func_vec.begin(), fe = func_vec.end(); fit != fe; ++fit, ++i) {
					if (highest < fit->second) {
						highest = fit->second;
						highest_index = i;
					}
				}
				Function* target = func_vec.at(highest_index).first;
				unsigned line_num = func_vec.at(highest_index).second;
				func_vec.erase(func_vec.begin() + highest_index);

				errs() << "Func: " << target->getName() << " line num: " << line_num << "\n";
				Function& F = *target;
				if (F.getName().str().find("__loop_bound__") == std::string::npos && F.getName().str().find("main") == std::string::npos) { // no loop bound, no main
					AttributeSet attr = F.getAttributes();
					if (!attr.hasAttrSomewhere(Attribute::NoInline)) {// no noinline
						if (noInline_counter < NOINLINE_NUM) {
							// do not inline
							noInline_counter++;

							// instead change the structure for future task-ifying
							errs() << "pretaskify " << F.getName() << "\n";
							F.setName("_PT_" + F.getName());
				//			preTaskify(&F);
						}
						else {
							// simply inline
							F.addFnAttr(Attribute::AlwaysInline);
						}
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
#if 0
		class CustomInLinePost : public ModulePass {
			public:
				static char ID;
				CustomInLinePost() : ModulePass(ID) { }
				void moveToMain(Function* F) {
					// 5. pad call with branch
					for (Value::user_iterator uit = F->user_begin(), ue = F->user_end(); uit != ue; ++uit) {
						// find the call point
						CallInst* callInst = dyn_cast<CallInst>(*uit);
						if (callInst != NULL) {
							BasicBlock::iterator bit = callInst;
							bit++;
							BranchInst* br = cast<BranchInst>(bit); // this MUST be branch (useless branch)!
							br->eraseFromParent();
							BranchInst* newBr = BranchInst::Create(&(F->front()), callInst);
							callInst->eraseFromParent();
						}
					}
					// 6. then, move the entire function bbs into main.
					for (auto &B : *F) {

					}
					// 7. and return with branch back
					// But these three step has to be executed after inlining > customInliningPost.cpp
				}
				virtual bool runOnModule(Module& M) {
					for (auto &F : M) {
						if (F.getName().str().find("__loop_bound__") == std::string::npos && F.getName().str().find("main") == std::string::npos) { // no loop bound, no main
							if (!attr.hasAttrSomewhere(Attribute::NoInline)) {// no noinline
								moveToMain(&F);
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
#endif
		char CustomInLine::ID = 1;
		//char* taskAnalysisID = &TaskAnalysis::ID;
		RegisterPass<CustomInLine> CIL("custominline", "Custom Inlining");
