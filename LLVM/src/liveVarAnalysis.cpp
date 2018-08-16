#include "include/liveVarAnalysis.h"
#include "include/tools.h"

value_vec* lva_vals;
Pass* callerPass;
std::map<Function*, Analysis*>* lva_liveVarResults;
std::map<Function*, unsigned> callNum;

/*
 * @brief: This function searches for all used var.
 * It should be called exactly only once
 */
void findAllVars(Module& M) {
	assert(lva_vals->size() == 0);
	for (auto &F : M) {
		if (!(F.getBasicBlockList().empty())) {
			// first seek local variables 
			for (Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {
				BasicBlock* block = FI;
				for (BasicBlock::iterator i = block->begin(), e = block->end(); i!=e; ++i) {
					Instruction *I = i;
					if (AllocaInst *alloca = dyn_cast<AllocaInst>(i)){ 
						(*lva_vals).push_back(alloca);
					}
				}
			}
			for (Value::user_iterator uit = F.user_begin(), ue = F.user_end(); uit != ue; ++uit) {
				// find the number of calls that specific function make
				CallInst* callInst = dyn_cast<CallInst>(*uit);
				if (callInst != NULL) {
					Function* callerFunc = callInst->getParent()->getParent();
					if (callNum.find(callerFunc) == callNum.end()) {
						callNum[callerFunc] = 1;
					}
					else {
						callNum[callerFunc]++;
					}
				}
			}
		}
	}

	for (auto &F : M) {
		if (!(F.getBasicBlockList().empty())) {
			if (callNum.find(&F) == callNum.end()) {
				callNum[&F] = 0;
			}
		}
	}
	// then global variables
	Module::GlobalListType& globalList = M.getGlobalList();	
	for (Module::GlobalListType::iterator GI = globalList.begin(); GI != globalList.end(); ++GI){
		// edge case. global var with address is memory-mapped I/O
		// assume that memory-mapped I/O is handled by init() function and do not track
		// also, constant (read-only) should not be cared.
		if (GI->getName().str().find("0x") == std::string::npos && !(GI->isConstant()) 
				&& GI->getName().str().find("overflow") == std::string::npos 
				&& GI->getName().str().find("chkpt_book") == std::string::npos 
				&& GI->getName().str().find("chkpt_status") == std::string::npos 
				&& GI->getName().str().find("CHKPT_NUM") == std::string::npos 
				&& GI->getName().str().find("curctx") == std::string::npos 
				&& GI->getName().str().find("curtask") == std::string::npos 
				&& GI->getName().str().find("chkpt_count") == std::string::npos 
				&& GI->getName().str().find("mode_status") == std::string::npos 
				&& GI->getName().str().find("_vector_timer0_b1") == std::string::npos 
				&& GI->getName().str().find("nv_cnt") == std::string::npos 
				&& GI->getName().str().find("max_backup") == std::string::npos ) {
			(*lva_vals).push_back(GI);
		}
	}
	// Print out the vars used in the function
	outs() << "Variable used by this module:\n";
	printSet(&(*lva_vals));
}

/*
 *	@brief: find var that always gets assigned to same constant
 *	and return bitVector of them
 */
value_vec analyzeConstant(Module& M) {
	value_vec alwaysConstantVars;
	// Those who only have one value has 1
	BitVector* alwaysConstantBV = new BitVector((*lva_vals).size());
	alwaysConstantBV->set();
	unsigned int j = 0;
	// Map to follow val--constant pair
	std::map<Value*, uint64_t> val_const_map;

	for (auto &F : M) {
		if (!F.getBasicBlockList().empty()) {
			AliasAnalysis* AA = &callerPass->getAnalysis<AAResultsWrapperPass>(F).getAAResults();
			for (auto &B: F) {
				for (auto &I : B) {
					// look for stores
					Value* v = NULL;
					Value* src;
					// TODO: need to handle about unknown function
					if (CallInst* ci = dyn_cast<CallInst>(&I)){
						if (isMemcpy(ci)) {
							v = ci->getOperand(0);
							src = ci->getOperand(1);
						}
					}
					else if (StoreInst *st = dyn_cast<StoreInst>(&I)) {
						v = st->getOperand(1);
						src = st->getOperand(0);
					}

					if (v != NULL) {
						j = 0;
						for(value_vec::iterator it = (*lva_vals).begin(); it != (*lva_vals).end(); ++it, ++j){
							// if it turned out to be not constant already, do not bother
							if (alwaysConstantBV->test(j)) {
								if (!isa<GlobalVariable>(*it)
										&& cast<Instruction>(*it)->getParent()->getParent()
										== I.getParent()->getParent()
										|| isa<GlobalVariable>(*it)) {
									AliasResult aresult = AA->alias(v,*it);
									// not Noalias + src not constant -> reset
									if (aresult != AliasResult::NoAlias) {
										if (ConstantInt* c = dyn_cast<ConstantInt>(src)) {
											// check if it gets a constant before && is the same constant
											uint64_t constVal = c->getSExtValue();
											if (val_const_map.find(*it) != val_const_map.end()) {
												// if prev val and cur val is different
												if (constVal != val_const_map.find(*it)->second) {
													alwaysConstantBV->reset(j);
												}
											}
											else {
												val_const_map[*it] = constVal;
											}
										}
										else {
											alwaysConstantBV->reset(j);
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
	j = 0;
	for(value_vec::iterator it = (*lva_vals).begin(); it != (*lva_vals).end(); ++it, ++j){
		if (alwaysConstantBV->test(j)) {
			alwaysConstantVars.push_back(*it);
		}
	}
	return alwaysConstantVars;
}

bool isDifferent(value_vec v1, value_vec v2) {
	unsigned i =0;
	for (value_vec::iterator VI = v1.begin(), VE = v1.end();
			VI != VE; ++VI, ++i) {
		if (isa<GlobalVariable>(*VI)) {
			if (*VI != v2.at(i)) {
				return true;
			}
		}
		else if (ConstantInt* ci = dyn_cast<ConstantInt>(*VI)) {
			ConstantInt* ci2 = cast<ConstantInt>(v2.at(i));
			if (ci->getSExtValue() != ci2->getSExtValue()) {
				return true;
			}
		}
		else {
			assert(false);
		}
	}
	return false;
}
/*
 *	@brief: find function local vars that takes ptr as an argument
 *	This is a common case that we want to optimize. (e.g., func(int* p))
 *	A lot of time the pointer itself is an address to specific dedicated
 *	location that cannot change (e.g., func(&a))
 *	In this case it does not needs protection for it can have only single
 *	write value
 */
value_vec analyzeConstLocalVar(Module& M) {
	value_vec alwaysConstLocalVar;
	// Those who only have one value has 1
	BitVector* alwaysConstLVBV = new BitVector((*lva_vals).size());
	alwaysConstLVBV->set();
	unsigned int j = 0;
	// Map to follow val--pointee pair
	std::map<Value*, value_vec> val_pointee_map;

	for (auto &F : M) {
		if (!F.getBasicBlockList().empty()) {
			AliasAnalysis* AA = &callerPass->getAnalysis<AAResultsWrapperPass>(F).getAAResults();
			for (auto &B: F) {
				for (auto &I : B) {
					// look for stores
					Value* v = NULL;
					Value* src;
					// TODO: need to handle about unknown function
					if (CallInst* ci = dyn_cast<CallInst>(&I)){
						if (isMemcpy(ci)) {
							v = ci->getOperand(0);
							src = ci->getOperand(1);
						}
					}
					else if (StoreInst *st = dyn_cast<StoreInst>(&I)) {
						v = st->getOperand(1);
						src = st->getOperand(0);
					}

					if (v != NULL) {
						j = 0;
						for(value_vec::iterator it = (*lva_vals).begin(); it != (*lva_vals).end(); ++it, ++j){
							// if it turned out to be not constant already, do not bother
							if (alwaysConstLVBV->test(j)) {
								if (!isa<GlobalVariable>(*it)
										&& cast<Instruction>(*it)->getParent()->getParent()
										== I.getParent()->getParent()
										|| isa<GlobalVariable>(*it)) {
									AliasResult aresult = AA->alias(v,*it);
									if (aresult != AliasResult::NoAlias) {
										if (isa<Argument>(src) && src->getType()->isPointerTy()) {
											// if it gets argument as a source && is a pointer
											Argument* arg = cast<Argument>(src);
											errs() << "arg: " << *src << "\n";
											errs() << "I: " << I << "\n";
											// Check if what can come as an argument
											Function* parentF = arg->getParent();
											// For all points that actually call this function
											for (Value::user_iterator uit = parentF->user_begin(),
													ue = parentF->user_end(); uit != ue; ++uit) {
												CallInst* usr = cast<CallInst>(*uit);
												// Get the var that gets passed at the caller site
												Value* callerArg = usr->getArgOperand(arg->getArgNo());
												value_vec callerArgVec;
												callerArgVec.push_back(callerArg);
												// 1. If it points to global variable (easiest)
												if (GlobalVariable* gv
														= dyn_cast<GlobalVariable>(callerArg)) {
													errs() << "case11\n";
													if (val_pointee_map.find(*it) != val_pointee_map.end()) {
														// if prev pointee and cur pointee is different
														if (isDifferent(callerArgVec, val_pointee_map.find(*it)->second)) {
															alwaysConstLVBV->reset(j);
															val_pointee_map.erase(*it);
														}
													}
													else {
														val_pointee_map[*it] = callerArgVec;
													}
												}
												// 2. If it is GEP operator to known global + constant offset
												else if (GEPOperator* gep = dyn_cast<GEPOperator>(callerArg)){
													// iffixed constant offset (known at compiler time)
													errs() << "case22\n";
													if (gep->hasAllConstantIndices()
															&& isa<GlobalVariable>(gep->getPointerOperand())) {
														errs() << "here1\n";
														GlobalVariable* pointee = cast<GlobalVariable>(gep->getPointerOperand());
														value_vec pointeeVec;
														pointeeVec.push_back(pointee);
														GEPOperator::op_iterator OIT = gep->idx_begin();
														++OIT;
														for (; OIT != gep->idx_end(); ++OIT) {
															if (ConstantInt* ci = dyn_cast<ConstantInt>(*OIT)) {
																pointeeVec.push_back(ci);
															}
															else {
																assert(false);
															}
														}
														if (val_pointee_map.find(*it) != val_pointee_map.end()) {
															errs() << "here2\n";
															// if prev pointee and cur pointee is different
															value_vec ref = val_pointee_map.find(*it)->second;
															if (isDifferent(pointeeVec, val_pointee_map.find(*it)->second)) {
																errs() << "here4\n";
																alwaysConstLVBV->reset(j);
																val_pointee_map.erase(*it);
															}
															else {
																errs() << "Same " << ref.at(0)->getName() << "\r\n";
															}
														}
														else {
															errs() << "here3\n";
															val_pointee_map[*it] = pointeeVec;
														}
													}
													else {
														alwaysConstLVBV->reset(j);
													}
												}
												else {
													alwaysConstLVBV->reset(j);
												}
											}
										}
										else {
											alwaysConstLVBV->reset(j);
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

	BitVector* alwaysConstLVBV2 = new BitVector((*lva_vals).size());
	alwaysConstLVBV2->set();
	BitVector* prev_alwaysConstLVBV2 = new BitVector(*alwaysConstLVBV2);
	// 3. More aggressively, when there is a load, track it based on upper result
	// e.g., func(p); where p = &a;
	while (true) {
		for (auto &F : M) {
			if (!F.getBasicBlockList().empty()) {
				AliasAnalysis* AA = &callerPass->getAnalysis<AAResultsWrapperPass>(F).getAAResults();
				for (auto &B: F) {
					for (auto &I : B) {
						// look for stores
						Value* v = NULL;
						Value* src;
						// TODO: need to handle about unknown function
						if (CallInst* ci = dyn_cast<CallInst>(&I)){
							if (isMemcpy(ci)) {
								v = ci->getOperand(0);
								src = ci->getOperand(1);
							}
						}
						else if (StoreInst *st = dyn_cast<StoreInst>(&I)) {
							v = st->getOperand(1);
							src = st->getOperand(0);
						}

						if (v != NULL) {
							j = 0;
							for(value_vec::iterator it = (*lva_vals).begin(); it != (*lva_vals).end(); ++it, ++j){
								// if it turned out to be not constant already, do not bother
								if (alwaysConstLVBV2->test(j)) {
									if (!isa<GlobalVariable>(*it)
											&& cast<Instruction>(*it)->getParent()->getParent()
											== I.getParent()->getParent()
											|| isa<GlobalVariable>(*it)) {
										AliasResult aresult = AA->alias(v,*it);
										if (aresult != AliasResult::NoAlias) {
											if (isa<Argument>(src) && src->getType()->isPointerTy()) {
												// if it gets argument as a source && is a pointer
												Argument* arg = cast<Argument>(src);
												// Check if what can come as an argument
												Function* parentF = arg->getParent();
												// For all points that actually call this function
												for (Value::user_iterator uit = parentF->user_begin(),
														ue = parentF->user_end(); uit != ue; ++uit) {
													CallInst* usr = cast<CallInst>(*uit);
													// Get the var that gets passed at the caller site
													Value* callerArg = usr->getArgOperand(arg->getArgNo());
													// if loadInst
													if (LoadInst* ld = dyn_cast<LoadInst>(callerArg)) {
														Value* pointee = ld->getOperand(0);
														// if loaded val is one of the var that we decided is
														// safe in previous
														if (val_pointee_map.find(pointee) != val_pointee_map.end()) {
															if (val_pointee_map.find(*it) != val_pointee_map.end()) {
																if (isDifferent(val_pointee_map.find(pointee)->second,
																			val_pointee_map.find(*it)->second)) {
																	val_pointee_map.erase(*it);
																	alwaysConstLVBV2->reset(j);
																}
															}
															else {
																val_pointee_map[*it] = val_pointee_map.find(pointee)->second;
															}
														}
														else {
															alwaysConstLVBV2->reset(j);
														}
													}
													else {
														alwaysConstLVBV2->reset(j);
													}
												}
											}
											else {
												alwaysConstLVBV2->reset(j);
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
		if (*alwaysConstLVBV2 == *prev_alwaysConstLVBV2) {
			break;
		}
		else {
			prev_alwaysConstLVBV2 = new BitVector(*alwaysConstLVBV2);
			alwaysConstLVBV2->set();
		}
	}

	j = 0;
	for(value_vec::iterator it = (*lva_vals).begin(); it != (*lva_vals).end(); ++it, ++j){
		if (alwaysConstLVBV->test(j)) {
			errs() << "no protection needed: " << (*it)->getName() << " in ";
			if (Instruction* II = dyn_cast<Instruction>(*it)) {
				errs() << II->getParent()->getParent()->getName() << "\n";
			}
			alwaysConstLocalVar.push_back(*it);
		}
	}

	j = 0;
	for(value_vec::iterator it = (*lva_vals).begin(); it != (*lva_vals).end(); ++it, ++j){
		if (alwaysConstLVBV2->test(j)) {
			errs() << "no protection needed2: " << (*it)->getName() << " in ";
			if (Instruction* II = dyn_cast<Instruction>(*it)) {
				errs() << II->getParent()->getParent()->getName() << "\n";
			}
			alwaysConstLocalVar.push_back(*it);
		}
	}
	errs() << "\n";
	return alwaysConstLocalVar;
}


/*
 *	@brief: this function do
 *	live var analysis for every instruction within M
 *	and return the result via lva_liveVarResults
 *	I know, the returning part is hacky
 */
void analyzeLiveVar(Module& M) {
	// initial condition	
	BitVector* init_in_b = new BitVector((*lva_vals).size());
	BitVector* init_out_b = new BitVector((*lva_vals).size());
	init_in_b->reset();
	init_out_b->reset();

	// build call tree
	while (1) {
		// break when the analyzing is done
		if (callNum.size() == 0) break;
		for (auto &F : M) {
			if (!(F.getBasicBlockList().empty())) {
				// We analyze from the innermost function
				// (who does not call another function that is not analyzed yet)
				if (callNum.find(&F) != callNum.end() && callNum[&F] == 0) {
					errs() << "analyzing function: " << F.getName() << "\n";
					//Testing
					Analysis* a = new Analysis(&F, 
							(*lva_vals), 
							init_in_b, //init of in (out[entry])
							init_out_b, //init of out (out[b])
							1, //is meet union? otherwise intersection
							0, //is forward analysis?
							&func); //transfer function
					(*lva_liveVarResults)[&F] = a;

					if (callNum.find(&F) != callNum.end()) {
						callNum.erase(&F);
					}

					for (Value::user_iterator uit = F.user_begin(), ue = F.user_end(); uit != ue; ++uit) {
						CallInst* callInst = dyn_cast<CallInst>(*uit);
						if (callInst != NULL) {
							Function* callerFunc = callInst->getParent()->getParent();
							if (callNum.find(callerFunc) == callNum.end()) {
								errs() << "caller is nowhere!\n";
								assert(false);
							}
							else {
								callNum[callerFunc]--;
								errs() << "call Num of " << callerFunc->getName() << " is now " << callNum[callerFunc] << "\n";
							}
						}
					}
				}
			}
		}
	}
}

void gen(Instruction *I, BitVector* gen_set){
	// before use, it should always load
	unsigned int j = 0;
	if (LoadInst *ld = dyn_cast<LoadInst>(I)){
		// get the alias analysis for current function

		AliasAnalysis* AAA = &callerPass->getAnalysis<AAResultsWrapperPass>(*(I->getParent()->getParent())).getAAResults();
		Value *v = ld->getOperand(0);
		j = 0;
		for(value_vec::iterator it = (*lva_vals).begin(); it != (*lva_vals).end(); ++it, ++j){
			// do not check if it is interprocedural local var (trivial)
			// TODO: what about global? In case of global does it goes into if? check (I hope so)
			if (!isa<GlobalVariable>(*it)) {
				Instruction* localVar = dyn_cast<Instruction>(*it);
				assert(localVar != NULL);
				if (localVar->getParent()->getParent() == I->getParent()->getParent()) {
					AliasResult result = AAA->alias(v,*it);

					// if it is not no alias (too naive?)
					if (result != AliasResult::NoAlias) {
						gen_set->set(j);
					}
				}
			}
			else {
				AliasResult result = AAA->alias(v,*it);

				// if it is not no alias (too naive?)
				if (result != AliasResult::NoAlias) {
					gen_set->set(j);
				}

			}
		}
	}

	// if it is callInst, add
	if (CallInst* callInst = dyn_cast<CallInst>(I)) {
		if (callInst->getCalledFunction() != NULL) {
			//			if (!(callInst->getCalledFunction()->getBasicBlockList().empty())) {
			if ((callInst->getCalledFunction()->getName().str().find("printf") == std::string::npos)) {
				// do live var analysis of the func and add it to gen
				Function* calledFunc = callInst->getCalledFunction();
				if (lva_liveVarResults->find(calledFunc) != lva_liveVarResults->end()) {
					(*gen_set) |= *((*lva_liveVarResults)[calledFunc]->get_inVector((calledFunc->front()).getFirstNonPHI()));
				}
				// argument of function call is considered gen for conservatism

				AliasAnalysis* AAA = &callerPass->getAnalysis<AAResultsWrapperPass>(*(I->getParent()->getParent())).getAAResults();
				for (unsigned i = 0; i < callInst->getNumArgOperands(); ++i) {
					Value* v = callInst->getArgOperand(i);
					j = 0;
					for(value_vec::iterator it = (*lva_vals).begin(); it != (*lva_vals).end(); ++it, ++j){
						// do not check if it is interprocedural local var (trivial)
						// TODO: what about global? In case of global does it goes into if? check (I hope so)
						if (!isa<GlobalVariable>(*it)) {
							Instruction* localVar = dyn_cast<Instruction>(*it);
							assert(localVar != NULL);
							if (localVar->getParent()->getParent() == I->getParent()->getParent()) {
								AliasResult result = AAA->alias(v,*it);

								// if it is not no alias (too naive?)
								if (result != AliasResult::NoAlias) {
									gen_set->set(j);
								}
							}
						}
						else {
							AliasResult result = AAA->alias(v,*it);

							// if it is not no alias (too naive?)
							if (result != AliasResult::NoAlias) {
								gen_set->set(j);
							}

						}
					}
				}
				//				}
				//				else {
				//					assert(false);
				//				}
		}
		}
	}
}

void kill(Instruction *I, BitVector* result){
	// kill is store (or memcpy or... )
	unsigned int j = 0;
	if (StoreInst *st = dyn_cast<StoreInst>(I)){
		AliasAnalysis* AAA = &callerPass->getAnalysis<AAResultsWrapperPass>(*(I->getParent()->getParent())).getAAResults();
		Value *v = st->getOperand(1);
		j = 0;
		for(value_vec::iterator it = (*lva_vals).begin(); it != (*lva_vals).end(); ++it, ++j){
			if (!isa<GlobalVariable>(*it)) {
				Instruction* localVar = dyn_cast<Instruction>(*it);
				assert(localVar != NULL);
				if (localVar->getParent()->getParent() == I->getParent()->getParent()) {
					AliasResult aresult = AAA->alias(v,*it);
					// if MustAlias
					if (aresult == AliasResult::MustAlias) {
						result->reset(j);
					}
				}
			}
			else {
				AliasResult aresult = AAA->alias(v,*it);
				// if MustAlias
				if (aresult == AliasResult::MustAlias) {
					result->reset(j);
				}
			}
		}
	}
#if 0 // this might have bugs..
	else if (CallInst* ci = dyn_cast<CallInst>(I)) {
		Function* calledF = ci->getCalledFunction();
		if (calledF) {
			if (calledF->getName().str().find("llvm.memcpy") != std::string::npos) {
				// get the alias analysis for current function
				//Constant* size = 
				//	ConstantInt::get(Type::getInt16Ty(M.getContext()), global_size);
				AliasAnalysis* AAA = &callerPass->getAnalysis<AAResultsWrapperPass>(*(I->getParent()->getParent())).getAAResults();
				Value *v = ci->getOperand(0);

				j = 0;
				for(value_vec::iterator it = (*lva_vals).begin(); it != (*lva_vals).end(); ++it, ++j){
					if (!isa<GlobalVariable>(*it)) {
						Instruction* localVar = dyn_cast<Instruction>(*it);
						assert(localVar != NULL);
						if (localVar->getParent()->getParent() == I->getParent()->getParent()) {
							AliasResult aresult = AAA->alias(v,*it);
							// if MustAlias
							if (aresult == AliasResult::MustAlias) {
								result->reset(j);
							}
						}
					}
					else {
						AliasResult aresult = AAA->alias(v,*it);
						// if MustAlias
						if (aresult == AliasResult::MustAlias) {
							result->reset(j);
						}
					}
				}
			}
		}
	}
#endif
	// TODO: You can also do CallInst analysis for optimization
	// However this is correct
	// I wonder if it will ever give MustAlias (especially without global)
}

BitVector* func(Instruction* I, BitVector* input){
	BitVector* result = new BitVector(*input);
	BitVector* gen_set = new BitVector(*input);
	gen_set->reset();
	unsigned int j = 0;
	// generate if variable is being used
	//AliasAnalysis& AA = getAnalysis<AAResultsWrapperPass>(*(I->getParent()->getParent())).getAAResults();
	//	errs() << "I: " << *I << "\n";
	gen(I, gen_set);
	kill(I, result);
#if 0
	for (User::op_iterator oit = I->op_begin(); oit != I->op_end(); ++oit){
		j = 0;
		for(value_vec::iterator it = lva_vals.begin(); it != lva_vals.end(); ++it, ++j){
			if(*it == *oit){
				gen_set->set(j);
			}
		}

	}
	j = 0;
	// kill if variable is being defined
	for(value_vec::iterator it = lva_vals.begin(); it != lva_vals.end(); ++it, ++j){
		if(*it == I)
			result->reset(j);
	}
	// Gen U (x - Kill)
#endif
	*result |= *gen_set;
	return result;
}
