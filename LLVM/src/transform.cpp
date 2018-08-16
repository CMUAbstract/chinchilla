#include "include/transform.h"
#include "include/analysis.h"
#include "include/tools.h"
#include "include/filterProtected.h"

using namespace llvm;

class TransformTask : public ModulePass {
	public:
		std::ofstream chkpt_log;
		static char ID;
		AllocaInst* dummy;
		std::vector<BitVector*> cutVar;
		//		value_vec renamed;
		node_vec doneRenamed;
		std::map<Value*, Value*> renamed;
		//node_vec starters;
		std::vector<Function*> nexttask;
		Function* checkpoint;
		Function* push_to_nvstack;
		Function* return_to_nvstack;
		node_vec doneTrans;
		value_vec globals;
		Function* check_before_write_may;
		Function* check_before_write_must;
		Function* check_before_write_must_uc;
		Function* make_table;
		unsigned checkpoint_idx = 0;
		// size of global var
		unsigned global_size = 0;
		unsigned mayAliasCnt = 0;
		unsigned mustAliasCnt = 0;
		value_vec backedUpGV;
		// this marks global that is actually used
		std::vector<GlobalVariable*> usedGlobal; 		
		TransformTask() : ModulePass(ID) { }

		// If backup of v is definitely present in bb
		bool isBackupPresent(BasicBlock* bb, Value* v) {
			for (auto &I : *bb) {
				if (CallInst* ci = dyn_cast<CallInst>(&I)) {
					if (ci->getCalledFunction() == check_before_write_must
							|| ci->getCalledFunction() == check_before_write_must_uc) {
						AliasAnalysis* AAA
							= &this->getAnalysis<AAResultsWrapperPass>(*(bb->getParent())).getAAResults();
						Value* v2 = ci->getOperand(0);
						AliasResult result = AAA->alias(v, v2);
						if (result == AliasResult::MustAlias) {
							return true;
						}
					}
				}
			}
			return false;
		}

		void add_init_to_main(Module& M) {
			for (auto &F : M) {
				if (F.getName().str().find("main") != std::string::npos) {
					Instruction* firstInst = &(F.front().front());
					Constant* c = 
						M.getOrInsertFunction("init",
								Type::getVoidTy(M.getContext()), 
								NULL);
					Function* init = cast<Function>(c);				
					c = 
						M.getOrInsertFunction("restore",
								Type::getVoidTy(M.getContext()), 
								NULL);
					Function* restore = cast<Function>(c);				

					value_vec args;
					CallInst::Create(init, ArrayRef<Value*>(args), "", firstInst);
					CallInst::Create(restore, ArrayRef<Value*>(args), "", firstInst);
				}
			}
		}
		void erase_unused_global(Module& M) {
			// unused globals also need to be removed!!
			std::vector<GlobalVariable*> unusedGlobal;
			Module::GlobalListType& globalList = M.getGlobalList();	
			for (Module::GlobalListType::iterator GI = globalList.begin(); 
					GI != globalList.end(); ++GI){
				// if global is constant
				if (GI->getNumUses() == 0) {
					if (std::find(usedGlobal.begin(), 
								usedGlobal.end(), GI) != usedGlobal.end()) 
						// only those who WAS USED BEFORE gets erased
						unusedGlobal.push_back(GI);
				}
			}
			for (gv_vec::iterator git = unusedGlobal.begin(), 
					ge = unusedGlobal.end(); git != ge; ++git) {
				(*git)->eraseFromParent();
			}
		}
		void constants_to_ro(Module& M) {
			// put constants to __ro_nv (for RAM overflowing issue)
			Module::GlobalListType& globalList = M.getGlobalList();	
			for (Module::GlobalListType::iterator GI = globalList.begin(); 
					GI != globalList.end(); ++GI){
				// if global is constant
				if (GI->isConstant()) {
					GI->setSection(".ro_nv_vars");
				}
			}
		}
		void erase_unused_inst(Module& M) {
			inst_vec needErase;
			// remove unused allocation
			for (auto &F : M) {
				for (auto &B : F) {
					for (auto &I : B) {
						if (AllocaInst* al = dyn_cast<AllocaInst>(&I)) {
							// if return inst and type not void
							if(al->user_empty()) {
								needErase.push_back(al);
							}
						}
					}
				}
			}
			for (inst_vec::iterator it = needErase.begin(), 
					e = needErase.end(); it != e; ++it) {
				(*it)->eraseFromParent();
			}
		}

		Module::global_iterator find_var_that_fits(unsigned size, 
				gv_vec* packed_gv, 
				Module& M) {
			Module::GlobalListType& gvars = M.getGlobalList();
			// first, search for exact match
			for (Module::GlobalListType::iterator git = gvars.begin(), 
					ge = gvars.end(); git != ge; ++git) {
				if (std::find(packed_gv->begin(), packed_gv->end(), git) 
						== packed_gv->end()) {
					if (get_size(git->getType()->getContainedType(0), &M) 
							== size) {
						return git;
					}
				}
			}
			// then, search for one that at least fits
			for (Module::GlobalListType::iterator git = gvars.begin(), 
					ge = gvars.end(); git != ge; ++git) {
				if (std::find(packed_gv->begin(), packed_gv->end(), git) 
						== packed_gv->end()) {
					if (get_size(git->getType()->getContainedType(0), &M) 
							< size) {
						return git;
					}
				}
			}
			return NULL; // if there is nothing fits
		}

		void allocate_chkpt_list(unsigned checkpoint_idx, 
				GlobalVariable* insert_before, 
				Module& M) {
			// declare chkpt_book
			std::vector<Constant*> initializer;
			// initialize as zero
			// Empty means zero
			make_global_array(M, 
					Type::getInt8Ty(M.getContext()), 
					checkpoint_idx, 
					new StringRef("chkpt_book"), 
					insert_before, 
					ArrayRef<Constant*>(initializer));

			// declare chkpt_status
			// initialize as zero
			// Empty means zero
			// TODO: for test, initialize as i
			for (unsigned i = 0; i < checkpoint_idx; ++i) {
				initializer.push_back(ConstantInt::get(Type::getInt16Ty(M.getContext()), 0xFFFF));
			}
			make_global_array(M,
					Type::getInt16Ty(M.getContext()),
					checkpoint_idx,
					new StringRef("chkpt_status"),
					insert_before,
					ArrayRef<Constant*>(initializer));

			// declare chkpt_list
			// First we need to declare struct that we will use
			/*
			std::vector<Type*> chkpt_info_elem;
			chkpt_info_elem.push_back(Type::getInt16Ty(M.getContext()));
			chkpt_info_elem.push_back(Type::getInt16PtrTy(M.getContext()));
			chkpt_info_elem.push_back(Type::getInt16Ty(M.getContext()));
			StructType* _chkpt_info = 
				StructType::get(M.getContext(),
						ArrayRef<Type*>(chkpt_info_elem));

			Constant* magic_number = 
				ConstantInt::get(Type::getInt16Ty(M.getContext()), 0x7777);
			Constant* magic_number_ptr = 
				ConstantExpr::getIntToPtr(magic_number, 
						PointerType::getUnqual
						(Type::getInt16Ty(M.getContext())));
			// init first 6 element to 0x7777
			initializer.push_back(magic_number);
			initializer.push_back(magic_number_ptr);
			initializer.push_back(magic_number);

			std::vector<Constant*> initializer_struct;
			Constant* magic_struct = 
				ConstantStruct::get(_chkpt_info, 
						ArrayRef<Constant*>(initializer));
			initializer_struct.push_back(magic_struct);

			initializer.clear();
			// init rest as zero
			Constant* zero_number = 
				ConstantInt::get(Type::getInt16Ty(M.getContext()), 0);
			Constant* zero_number_ptr = 
				ConstantExpr::getIntToPtr(zero_number, 
						PointerType::getUnqual
						(Type::getInt16Ty(M.getContext())));
			initializer.push_back(zero_number);
			initializer.push_back(zero_number_ptr);
			initializer.push_back(zero_number);

			Constant* zero_struct = 
				ConstantStruct::get(_chkpt_info, 
						ArrayRef<Constant*>(initializer));
			// except for the first, all is zero
			for (unsigned i = 0; i < checkpoint_idx - 1; ++i) {
				initializer_struct.push_back(zero_struct);
			}

			make_global_array(M, 
					_chkpt_info, 
					checkpoint_idx, 
					new StringRef("chkpt_list"), 
					insert_before, 
					ArrayRef<Constant*>(initializer_struct));
			*/
			// set CHKPT_NUM
			Constant* CHKPT_NUM = 
				ConstantInt::get(Type::getInt16Ty(M.getContext()), 
						checkpoint_idx);
			new GlobalVariable(M, 
					Type::getInt16Ty(M.getContext()), 
					false, 
					GlobalValue::ExternalLinkage, 
					CHKPT_NUM, 
					"CHKPT_NUM");
		}

		bool isCutVarOrGlobal(Value* v){
			// to fill usedGlobal,
			if (GlobalVariable* gv = dyn_cast<GlobalVariable>(v)) {
				if (std::find(usedGlobal.begin(), usedGlobal.end(), gv)
						== usedGlobal.end())
					usedGlobal.push_back(gv);
			}
			int val_index = -1;
			for(unsigned i = 0; i < vals.size(); ++i) {
				if (vals.at(i) == v){
					val_index = i;
				}
			}
			if (val_index != -1) {
				for (std::vector<BitVector*>::iterator it = cutVar.begin(),
						e = cutVar.end(); it != e; ++it){
					BitVector* out_bit = *it;
					if(out_bit->test(val_index))
						return true;

				}
			}
			return false;
		}

		Value* getOrCreateRenamedVar(Module& M, Node* curNode, Value* var) {
			Value* v;
			Constant* initializer;
			Twine* name;
			// non protected vars go before here
			GlobalVariable* insertBefore = cast<GlobalVariable>(M.getNamedValue("curctx"));

			if(AllocaInst* def = dyn_cast<AllocaInst>(var)) {
				if (needsProtection(var)) {
					v = M.getNamedValue(("_global_"+def->getName()+
								"_"+curNode->getMother()->getName()).str());
				}
				else {
					v = M.getNamedValue(("_np_"+def->getName()+
								"_"+curNode->getMother()->getName()).str());
				}
				initializer = Constant::getNullValue(def->getType()->getContainedType(0));
				if(v != NULL){
					return v;
				}
				else if (isCutVarOrGlobal(var)){
					if (needsProtection(var)) {
						name = new Twine("_global_"+ var->getName()
								+ "_"+curNode->getMother()->getName());
						GlobalVariable* gVar = make_global_considering_layout(M,
								var->getType()->getContainedType(0), *name,
								initializer);
						return gVar;
					}
					else {
						name = new Twine("_np_" + var->getName()+ "_"+curNode->getMother()->getName());
						GlobalVariable* gVar = make_global(M,
								var->getType()->getContainedType(0), *name, insertBefore,
								initializer);
						return gVar;
					}
				}
			}
			else if (GlobalVariable* def = dyn_cast<GlobalVariable>(var)){
				// edge case. global var with address is memory-mapped I/O
				// assume that memory-mapped I/O is
				// handled by init() function and do not track
				// also, constant (read-only) should not be cared.
				if (def->getName().str().find("0x") == std::string::npos
						&& !(def->isConstant())) {
					if (needsProtection(var)) {
						v = M.getNamedValue(("_global_"+def->getName()).str());
					}
					else {
						v = M.getNamedValue(("_np_"+def->getName()).str());
					}
					if(v != NULL){
						return v;
					}
					else if (isCutVarOrGlobal(var)){
						initializer = def->getInitializer();
						if (needsProtection(var)) {
							name = new Twine("_global_"+ var->getName());
							// Protected Var
							GlobalVariable* gVar = make_global_considering_layout(M,
									var->getType()->getContainedType(0), *name,
									initializer);
							return gVar;
						}
						else {
							name = new Twine("_np_" + var->getName());
							// non-protected Var
							GlobalVariable* gVar = make_global(M,
									var->getType()->getContainedType(0), *name, insertBefore,
									initializer);
							return gVar;
						}
					}
				}
				else {
					return NULL;
				}
			}
			else {
				return NULL;
			}
		}

		void renameVar(Node* curNode, Module &M) {
			BasicBlock* curBB = curNode->getBB();
			// TODO: 1) clean up this code please...
			// 2) Instead of making everything protected,
			// make a function that decides whether it needs protection
			// or whether it only needs to be NV and that is it.
			// And call make_global_considering... to only protected

			for (BasicBlock::iterator bit = curBB->begin(),
					be = curBB->end(); bit != be; ++bit) {
				Instruction* I = dyn_cast<Instruction>(bit);
				assert(I != NULL);

				for (unsigned i = 0; i < I->getNumOperands(); ++i) {
					Value* var = I->getOperand(i);
					Value* newVar = NULL;

					// edge case: call(bitcast @a to i8*,...)
					if (BitCastOperator* bc = dyn_cast<BitCastOperator>(var)) {
						Value* bcVal = bc->getOperand(0);
						Value* v = getOrCreateRenamedVar(M, curNode, bcVal);
						if (v != NULL) {
							newVar = new BitCastInst(v, bc->getDestTy(), "bitcast", I);
						}
					}
					// edge case: for example, store 1, getelementptr %0, ....
					else if(GEPOperator* gep = dyn_cast<GEPOperator>(var)){
						Value* gepVal = gep->getPointerOperand();
						Value* v = getOrCreateRenamedVar(M, curNode, gepVal);
						if (v != NULL) {
							value_vec arrayRef;
							for (User::op_iterator uit = gep->idx_begin(),
								 	ue = gep->idx_end(); uit != ue; ++uit){
								arrayRef.push_back(uit->get());
							}
							newVar = GetElementPtrInst::CreateInBounds(v,
									ArrayRef<Value*>(arrayRef), "", I);
						}
					}
					// Normal case
					else {
						newVar = getOrCreateRenamedVar(M, curNode, var);
					}

					if (newVar != NULL) {
						I->setOperand(i, newVar);
					}
				}
			}
		}

		/*
		 * @brief this function estimates all the cutvar of a given function's
		 * call site and call site of call site and ...
		 * and return the bitvector
		 */
		BitVector* getCutVarOfCallers(Function* F) {
			BitVector* result = new BitVector(vals.size());
			result->reset();

			for (Value::user_iterator UI = F->user_begin(),
					UE = F->user_end(); UI != UE; ++UI) {
				if (CallInst* ci = dyn_cast<CallInst>(*UI)) {
					Node* node = findNode(ci->getParent());
					BitVector* bv = liveVarResult[ci->getParent()->getParent()]
						->get_outVector(ci);

					(*result) |= (*bv);

					Function* callerFunc = ci->getParent()->getParent();
					BitVector* bv2 = getCutVarOfCallers(callerFunc);
					(*result) |= (*bv2);
				}
			}

			return result;
		}

		/*
		 * @brief function that adds cehckpoint on every cutted edge
		 */
		void addCheckpoint(Node* curNode, Module &M) {
			edge_vec out_edges = curNode->getOutEdges();
			for (edge_vec::iterator oit = out_edges.begin(),
					oe = out_edges.end(); oit != oe; ++oit) {
				if (((*oit)->checkIsCut())) {
					BitVector* bv = (*oit)->getOutCutVars();
					/*
					 * here, we dump the bv of each checkpoint as well
					 * for later use
					 */
					cutVar.push_back(bv);

					BitVector* bv_final = bv;
					// If this is a function that is not main, we should also
					// add the variable that lives across the callsite of this
					// function because that is also effectively a cut location
					// And also the call site of the call site of the ...
					Function* curF = curNode->getBB()->getParent();
					BitVector* bv_callsite = getCutVarOfCallers(curF);
					// TODO: THis is really inefficient.
					// We should not add bv to cutVar multiple times
					cutVar.push_back(bv_callsite);
					(*bv_final) |= (*bv_callsite);


					chkpt_log << checkpoint_idx << ":";
					for (unsigned i = 0; i < bv_final->size(); ++i) {
						chkpt_log << bv_final->test(i);
					}
					chkpt_log << "\n";

					TerminatorInst* jmp_to_next = NULL;
					if (BranchInst* br = 
							dyn_cast<BranchInst>(&((*oit)->getSrc()->getBB()->back()))) {
						jmp_to_next = br;
					}
					else if (SwitchInst* sw = 
							dyn_cast<SwitchInst>(&((*oit)->getSrc()->getBB()->back()))) {
						jmp_to_next = sw;
					}

					assert(jmp_to_next != NULL);
#if 1 // KIWAN: CHECKPOINT DISABLE
					BasicBlock* condBB = BasicBlock::Create(M.getContext(),
							"condBB",
							curNode->getBB()->getParent(),
							(*oit)->getDest()->getBB());
					BasicBlock* newBB = BasicBlock::Create(M.getContext(),
							"newBB",
							curNode->getBB()->getParent(),
							(*oit)->getDest()->getBB());

					// case 1. Naive approach
#if 0
					// although it might introduce overhead, 
					// for tracking, debugging and various fun stuff,
					// save the checkpoint index on curctx->cur_reg[15]
					Value* curctx = M.getNamedValue("curctx");
					LoadInst* ldr = new LoadInst(curctx, "", true, newBB);
					value_vec args;
					Constant* zero = 
						Constant::getNullValue(Type::getInt32Ty(M.getContext()));
					args.push_back(zero);
					args.push_back(zero);
					GetElementPtrInst* gep = 
						GetElementPtrInst::CreateInBounds(ldr, 
								ArrayRef<Value*>(args), "cur_reg", newBB);
					ldr = new LoadInst(gep, "", newBB);
					args.clear();
					Constant* last = 
						ConstantInt::get(Type::getInt32Ty(M.getContext()), 15);
					args.push_back(last);
					gep = GetElementPtrInst::CreateInBounds(ldr, 
							ArrayRef<Value*>(args), "arrayidx", newBB);
					Constant* check_idx = 
						ConstantInt::get(Type::getInt16Ty(M.getContext()), checkpoint_idx);
					StoreInst* str = new StoreInst(check_idx, gep, newBB);
#endif

					// case 2. hysteresis analysis
#if 0
					// chkpt_book[check_idx]++;
					Value* book = M.getNamedGlobal("chkpt_book");
					Constant* check_idx = 
						ConstantInt::get(Type::getInt16Ty(M.getContext()), checkpoint_idx);
					Constant* zero = 
						Constant::getNullValue(Type::getInt16Ty(M.getContext()));
					value_vec args;
					args.push_back(zero);
					args.push_back(check_idx);
					errs() << "gep1\n";
					GetElementPtrInst* gep = 
						GetElementPtrInst::CreateInBounds(book, 
								ArrayRef<Value*>(args), "arrayidx", newBB);

					LoadInst* ldr = new LoadInst(gep, "", newBB);
					Constant* one = ConstantInt::get(Type::getInt16Ty(M.getContext()), 1);
					BinaryOperator* inc = 
						BinaryOperator::Create(Instruction::Add, ldr, one, "inc", newBB);
					StoreInst* str = new StoreInst(inc, gep, newBB);

					// cur_reg[15] = chkpt_idx;
					Value* curctx = M.getNamedValue("curctx");
					ldr = new LoadInst(curctx, "", true, newBB);
					args.clear();
					zero = Constant::getNullValue(Type::getInt32Ty(M.getContext()));
					args.push_back(zero);
					args.push_back(zero);
					errs() << "gep2\n";
					gep = GetElementPtrInst::CreateInBounds(ldr, ArrayRef<Value*>(args), "cur_reg", newBB);
					ldr = new LoadInst(gep, "", newBB);
					args.clear();
					Constant* last = ConstantInt::get(Type::getInt32Ty(M.getContext()), 15);
					args.push_back(last);
					errs() << "gep3\n";
					gep = GetElementPtrInst::CreateInBounds(ldr, ArrayRef<Value*>(args), "arrayidx", newBB);
					str = new StoreInst(check_idx, gep, newBB);
#endif

					// case 3. prev-and-cur analysis
					// When reboot on checkpoint, it gets score 1 and prev gets -1 (because one of the two nearby checkpoint must die)
#if 1
					// save the checkpoint index on curctx->cur_reg[15]
//					Value* curctx = M.getNamedValue("curctx");
//					LoadInst* ldr = new LoadInst(curctx, "", true, newBB);
					value_vec args;
//					Constant* zero = Constant::getNullValue(Type::getInt32Ty(M.getContext()));
//					args.push_back(zero);
//					args.push_back(zero);
//					GetElementPtrInst* gep = GetElementPtrInst::CreateInBounds(ldr, ArrayRef<Value*>(args), "cur_reg", newBB);
//					ldr = new LoadInst(gep, "", newBB);
//					args.clear();
//					Constant* last = ConstantInt::get(Type::getInt32Ty(M.getContext()), 15);
//					args.push_back(last);
//					gep = GetElementPtrInst::CreateInBounds(ldr, ArrayRef<Value*>(args), "arrayidx", newBB);
//					Constant* check_idx = ConstantInt::get(Type::getInt16Ty(M.getContext()), checkpoint_idx);
//					StoreInst* str = new StoreInst(check_idx, gep, newBB);
#endif
					//value_vec args;
					args.clear();
					CallInst* call = CallInst::Create(checkpoint, 
							ArrayRef<Value*>(args), "", newBB);
					BranchInst* newBr = 
						BranchInst::Create((*oit)->getDest()->getBB(), newBB);

#if 1

#if 0 // count the number of basic block crossing
					Value* bb_cnt = M.getNamedValue("nv_cnt");
					LoadInst* bb_ldr = new LoadInst(bb_cnt, "", condBB);

					Constant* one = ConstantInt::get(Type::getInt32Ty(M.getContext()), 1);
					BinaryOperator* inc =
						BinaryOperator::Create(Instruction::Add, bb_ldr, one, "inc", condBB);
					StoreInst* str = new StoreInst(inc, bb_cnt, condBB);

#endif
					// For recovery.. this may be expensive...!!
					Value* timer_status = M.getNamedValue("timer_expired");
					LoadInst* timer_ldr = new LoadInst(timer_status, "", condBB);
					Constant* one8 =
						ConstantInt::get(Type::getInt8Ty(M.getContext()), 1);
						//Constant::getNullValue(Type::getInt8Ty(M.getContext()));
					ICmpInst* icmp =
							new ICmpInst(*condBB, CmpInst::ICMP_EQ, timer_ldr, one8, "tobool");
					BranchInst* condBr =
						BranchInst::Create(newBB, (*oit)->getDest()->getBB(), icmp, condBB);
#endif
					checkpoint_idx++;

					//					// fix if successor has phi node
					for (unsigned i = 0; i < jmp_to_next->getNumSuccessors(); ++i) {
						if (jmp_to_next->getSuccessor(i) == (*oit)->getDest()->getBB()) {
							jmp_to_next->setSuccessor(i, condBB);
							//						br->setSuccessor(i, newBB);
						}
					}

					for (BasicBlock::iterator pit = (*oit)->getDest()->getBB()->begin(), 
							pe = (*oit)->getDest()->getBB()->end(); pit != pe; ++pit) {
						PHINode* phi = dyn_cast<PHINode>(pit);
						if (phi) {
							for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
								if (phi->getIncomingBlock(i) == curNode->getBB()) {
									phi->setIncomingBlock(i, newBB);
									phi->addIncoming(phi->getIncomingValue(i), condBB);
								}
							}
						}
					}
#endif // KIWAN: CHKPT DISABLE
				}
			}
		}

		void insert_cbw(Instruction* I, BitVector* in_bitvec, Value* v, Node* curNode) {
			AliasAnalysis* AAA
				= &this->getAnalysis<AAResultsWrapperPass>(*(I->getParent()->getParent())).getAAResults();
			unsigned j = 0;
			errs() << *I << "\n";
			for(value_vec::iterator it = globals.begin(); it != globals.end(); ++it, ++j){
				// if the result is 1, no need to version that global
				if (in_bitvec->test(j) == 0) {
					// only do for result 0
					AliasResult result = AAA->alias(v,*it);
					if (result != AliasResult::NoAlias) {
#if 1
						// Optimization for May and Must Alias
						if (result == AliasResult::MustAlias) {
							errs() << "Must: " << (*it)->getName() << "\n";
#if 1 // KIWAN: tight loop optimization disabled
							if (MyLoop* loop = isInTightLoop(curNode)) {
								// Optimization
								// For tight loop, we do some optimizing
								if (loop->isBackedupByLoop(*it)) {
									// do nothing
								}
								else {
									// mark the variable as covered by loop
									loop->addBackedupByLoop(*it);

									// and take care of it later...
								}
							}
							else {
#endif
								CastInst* cast = CastInst::CreatePointerCast(v,
										Type::getInt8PtrTy(I->getParent()->getParent()->getContext()), "", I);
								value_vec args;
								args.clear();
								args.push_back(cast);
								CallInst* call = CallInst::Create(check_before_write_must, ArrayRef<Value*>(args), "", I);
#if 1 // KIWAN: tight loop optimization disabled
							}
#endif
						}
						else if (result == AliasResult::MayAlias) {
							CastInst* cast = CastInst::CreatePointerCast(v,
									Type::getInt8PtrTy(I->getParent()->getParent()->getContext()), "", I);
							value_vec args;
							args.clear();
							args.push_back(cast);
							CallInst* call = CallInst::Create(check_before_write_may, ArrayRef<Value*>(args), "", I);
						}
						else {
							assert(false);
						}
#endif // KIWAN: UNDO LOGGING DISABLED
						break;
					}
				}
			}
		}

		/*
		 * @brief: This function checks whether specific write (store)
		 * is writing to global NV region or not
		 * and inserts check_before_write accordingly
		 * But if previous basicblock have already done it,
		 * it does not do it (in_bitvec check)
		 * TODO: there is an optimization point because
		 * sometimes you don't need to check_before_write
		 * because you are writing for the first time
		 */
		void dynamicVersioning(Node* curNode, node_vec *visitedNode) {
			visitedNode->push_back(curNode);

			BasicBlock* curBB = curNode->getBB();
			//errs() << curBB->getName() << "\n";

			BitVector* in_bitvec = new BitVector(globals.size());
			edge_vec in_edges = curNode->getInEdges();
			if (in_edges.size() == 0) {
				in_bitvec->reset();
			}
			else {
				in_bitvec->set();
			}
			for (edge_vec::iterator iit = in_edges.begin(), ie = in_edges.end(); iit != ie; ++iit) {
				if ((*iit)->checkIsCut()) {
					in_bitvec->reset();
				}
				else {
					if ((*iit)->getSrc()->getVersionBitmask() != NULL) {
						// those who was already privatized by the prev bitvec
						// will have 1, so if every prev bb did check_before_write
						// for certain var, it will be 1
						*in_bitvec &= *((*iit)->getSrc()->getVersionBitmask());
					}
					else {
						assert(false);
					}
				}
			}

			// TODO: do we really need this line??
			*in_bitvec &= *(curNode->getVersionBitmask());

			for (auto &I : *curBB) {
				if (StoreInst* si = dyn_cast<StoreInst>(&I)) {
					// get the alias analysis for current function
					Value *v = si->getOperand(1);

					insert_cbw(si, in_bitvec, v, curNode);
				}
				// deal with memcpy!
				else if (isMemcpy(&I)) {
					CallInst* ci = dyn_cast<CallInst>(&I);
					Value *v = ci->getOperand(0);
					insert_cbw(ci, in_bitvec, v, curNode);
				}
				// TODO: what about function calls?
				// Function call is an optimization
				// It is currently correct itself
				// (Though it might be slow)
			}

			edge_vec out_edges = curNode->getOutEdges();
			for (edge_vec::iterator oit = out_edges.begin(), oe = out_edges.end(); oit != oe; ++oit) {
				if (std::find(visitedNode->begin(), visitedNode->end(), (*oit)->getDest()) == visitedNode->end() ){
					dynamicVersioning((*oit)->getDest(), visitedNode);
				}
			}

		}

		/*
		 *	@brief: This code checks the must alias between writes to global
		 *	within checkpoint region
		 *	However it only checks across tasks. Not within tasks I guess (TODO)
		 */
		bool buildVersioningTree(Node* curNode, node_vec *visitedNode) {
			bool changed = false;
			visitedNode->push_back(curNode);

			BasicBlock* curBB = curNode->getBB(); 
			if ((curNode->getVersionBitmask() == NULL)) {
				curNode->initVersionBitmask(globals.size());
			}
			BitVector* prev = new BitVector(*(curNode->getVersionBitmask()));

			for (auto &I : *curBB) {
				// TODO: Lots of inefficiency, do aliasing!!!!!
				if (StoreInst* si = dyn_cast<StoreInst>(&I)) {

					// get the alias analysis for current function
					Value *v = si->getOperand(1);
					AliasAnalysis* AAA = &this->getAnalysis<AAResultsWrapperPass>(*(curBB->getParent())).getAAResults();
					unsigned j = 0;
					for(value_vec::iterator it = globals.begin(); it != globals.end(); ++it, ++j){
						AliasResult result = AAA->alias(v,*it);
						if (result == AliasResult::MustAlias) {
							// if you may write to certain element, you set it as 1
							curNode->setVersionBitmask(j);
						}
					}
				}
				// TODO: what about function calls?
				// I guess it is an optimization. It will be correct
			}
			edge_vec in_edges = curNode->getInEdges();
			BitVector* in_bitvec = new BitVector(globals.size());
			if (in_edges.size() == 0) {
				in_bitvec->reset();
			}
			else {
				in_bitvec->set();
			}
			for (edge_vec::iterator iit = in_edges.begin(), ie = in_edges.end(); iit != ie; ++iit) {
				if ((*iit)->checkIsCut()) {
					in_bitvec->reset();
				}
				else {
					if ((*iit)->getSrc()->getVersionBitmask() != NULL) {
						// if every prev bb writes to certain var, it is 1
						*in_bitvec &= *((*iit)->getSrc()->getVersionBitmask());
					}
					else {
						// considered as 0
						in_bitvec->reset();
					}
				}
			}
			// if you write specific var in every prev bb,
			// you also set it as 1 because later on you don't want
			// any check_before_write to happen
			*(curNode->getVersionBitmask()) |= *in_bitvec;

			changed = *(curNode->getVersionBitmask()) != *prev;

			edge_vec out_edges = curNode->getOutEdges();
			for (edge_vec::iterator oit = out_edges.begin(), oe = out_edges.end(); oit != oe; ++oit) {
				if (std::find(visitedNode->begin(), visitedNode->end(), (*oit)->getDest()) == visitedNode->end() ){
					changed |= buildVersioningTree((*oit)->getDest(), visitedNode);
				}
			}
			return changed;
		}

		void declare_lib_globals(Module& M) {
			//GlobalVariable* status = 
			//	new GlobalVariable(M, 
			//			ArrayType::get(Type::getInt8Ty(M.getContext()), 65), 
			//			false, GlobalValue::CommonLinkage, 0, 
			//			Twine(*(new StringRef("chkpt_status"))), NULL,
			//			GlobalValue::ThreadLocalMode::NotThreadLocal, 0, true);
			//status->setInitializer(Constant::getNullValue(ArrayType::get(Type::getInt8Ty(M.getContext()), 65)));	

//			GlobalVariable* status = new GlobalVariable(M,
//					Type::getInt16Ty(M.getContext()),
//					false, GlobalValue::CommonLinkage, 0,
//					Twine(*(new StringRef("mode_status"))), NULL,
//					GlobalValue::ThreadLocalMode::NotThreadLocal, 0, true);

			GlobalVariable* timer = new GlobalVariable(M,
					Type::getInt8Ty(M.getContext()),
					false, GlobalValue::CommonLinkage, 0,
					Twine(*(new StringRef("timer_expired"))), NULL,
					GlobalValue::ThreadLocalMode::NotThreadLocal, 0, true);
			timer->setInitializer(Constant::getNullValue(Type::getInt8Ty(M.getContext())));	

		}

		LoadInst* privAndRestore(BasicBlock* bb, Value* localVar) {
			CallInst* call = NULL;
			for (auto &I : *bb) {
				// get Checkpoint
				call = dyn_cast<CallInst>(&I);
				if (call && call->getCalledFunction()->getName().str().find("checkpoint") != std::string::npos) {
					break;
				}
			}
			assert(call != NULL);

			// make new global region (TODO: this can be reused)
			std::string name = "_global_phi_" + bb->getName().str();
			name += "_";

			if (Instruction* I = dyn_cast<Instruction>(localVar)) {
				// if I's name is invalid (true = -1 / TODO: false?)
				name += I->getName();
				Constant* zero = Constant::getNullValue(I->getType());
				GlobalVariable* gVar = 
					make_global_considering_layout(*(bb->getParent()->getParent()), 
							I->getType(), name, zero);

				CastInst* cast = CastInst::CreatePointerCast(gVar, 
						Type::getInt8PtrTy(bb->getParent()->getParent()->getContext()), "", call);
				value_vec args;
				args.clear();
				args.push_back(cast);
				//
				CallInst::Create(check_before_write_must, ArrayRef<Value*>(args), "", call);
				// insert global region <- localVar before checkpoint
				StoreInst* str = new StoreInst(I, gVar, call);

				// insert localVar <- global region after checkpoint
				BasicBlock::iterator bit = BasicBlock::iterator(call);
				bit++;
				Instruction* nextInst = dyn_cast<Instruction>(bit);
				return new LoadInst(gVar, "", nextInst);
			}
			else if (ConstantInt* C = dyn_cast<ConstantInt>(localVar)) {
				if (C->getSExtValue() >= 0) {
					name += std::to_string(C->getSExtValue());
				}
				else {
					// cant use - sign in name. it is invalid
					name += "m";
					name += std::to_string(-(C->getSExtValue()));
				}
				Constant* zero = Constant::getNullValue(C->getType());
				GlobalVariable* gVar = 
					make_global_considering_layout(*(bb->getParent()->getParent()), 
							C->getType(), name, zero);

				// insert global region <- localVar before checkpoint
				StoreInst* str = new StoreInst(C, gVar, call);

				// insert localVar <- global region after checkpoint
				BasicBlock::iterator bit = BasicBlock::iterator(call);
				bit++;
				Instruction* nextInst = dyn_cast<Instruction>(bit);
				return new LoadInst(gVar, "", nextInst);

			}
			else {
				assert(false);
				return NULL;
			}
		}

		void fixPhiNode(Module& M) {
			for (auto &F : M) {
				for (auto &B : F) {
					for (auto &I : B) {
						// if phi node
						if (PHINode* phi = dyn_cast<PHINode>(&I)) {
							// for removing checkpoint and skipping BBs, we add one
							// dummy BB which will be used for jumping over chekcpoints with Phi
							for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
								// if not constant, we need to save and restore this on checkpoint
								// Even if constant, we have to deal with it because the stupid Clang
								// uses stack instead of using constant.
								// Woooah!!!!!!!
								//if (!isa<Constant>(phi->getIncomingValue(i))) {
								BasicBlock* prevBB = phi->getIncomingBlock(i);
								// it is either condBB or newBB. Our interest is newBB (where checkpoint lies)
								if (prevBB->getName().str().find("newBB") != std::string::npos) {
									//BasicBlock* bbForPhi = BasicBlock::Create(M.getContext(), "bbForPhi", &F, &B);
									//BranchInst::Create(&B, bbForPhi);

									// what value should we use if we come from bbForPhi
									//phi->addIncoming(phi->getIncomingValue(i), bbForPhi);

									// when checkpointing, read from NV saved value
									LoadInst* ldr = privAndRestore(prevBB, phi->getIncomingValue(i));
									phi->setIncomingValue(i, ldr);
								}
								//}
							}
						}
					}
				}
			}
		}

		/*
		 * @brief this is the main pass
		 */
		virtual bool runOnModule(Module& M) {
			declare_lib_globals(M);
			// allocate arrays
			// TEMP DISABLE!!
			allocate_chkpt_list(totalCut, NULL, M);

			Constant* c = M.getOrInsertFunction("checkpoint",
					llvm::Type::getVoidTy(M.getContext()), 
					NULL);
			checkpoint = cast<Function>(c);				

			c = M.getOrInsertFunction("push_to_nvstack",
					llvm::Type::getVoidTy(M.getContext()), 
					NULL);
			push_to_nvstack = cast<Function>(c);				

			c = M.getOrInsertFunction("return_to_nvstack",
					llvm::Type::getVoidTy(M.getContext()), 
					NULL);
			return_to_nvstack = cast<Function>(c);				

			// Var for unrolling
			//Constant* zero16 = Constant::getNullValue(Type::getInt16Ty(M.getContext()));
			//loopVar = make_global_considering_layout(M,
			//	 	Type::getInt16Ty(M.getContext()), *(new Twine("_global_kw_loopVar")), zero16);
			//starters.push_back(entryNode);

			// log the chkpt and its corresponding cut vars
			// for later optimization
			chkpt_log.open("./chkpt_bv.log");
			for(unsigned i = 0; i < vals.size(); ++i){
				chkpt_log << "_global_";
				chkpt_log << vals.at(i)->getName().str();
				if (AllocaInst* alloc = dyn_cast<AllocaInst>(vals.at(i))) {
					chkpt_log << "_" << alloc->getParent()->getParent()->getName().str();
				}
				chkpt_log << ",";
			}
			chkpt_log << "\n";
			// iterate every node (BB) and if it needs chkpt, place it
			for (node_vec::iterator it = allNode.begin(),
					e = allNode.end(); it != e; ++it) {
				addCheckpoint(*it, M);
			}
			chkpt_log.close();

			// iterate every node and promote to global when needed
			for (node_vec::iterator it = allNode.begin(),
					e = allNode.end(); it != e; ++it) {
				renameVar(*it, M);
			}


			c = M.getOrInsertFunction("check_before_write_may",
					Type::getVoidTy(M.getContext()),
					Type::getInt8PtrTy(M.getContext()),
					NULL);
			check_before_write_may = cast<Function>(c);
			// Optimized version for mustAlias
			c = M.getOrInsertFunction("check_before_write_must",
					Type::getVoidTy(M.getContext()),
					Type::getInt8PtrTy(M.getContext()),
					NULL);
			check_before_write_must = cast<Function>(c);
			c = M.getOrInsertFunction("check_before_write_must_unconditional",
					Type::getVoidTy(M.getContext()),
					Type::getInt8PtrTy(M.getContext()),
					NULL);
			check_before_write_must_uc = cast<Function>(c);
			// fix exception case of phi nodes
			fixPhiNode(M);

			erase_unused_inst(M);
			constants_to_ro(M);
			erase_unused_global(M);

			add_init_to_main(M);

			// add DynamicVersioning.cpp here
			// check global range
			Module::GlobalListType& gvars = M.getGlobalList();
			GlobalValue* begin = NULL;
			GlobalValue* end = NULL;
			for (Module::GlobalListType::iterator git = gvars.begin(), 
					ge = gvars.end(); git != ge; ++git) {
				if ((git->getName().str().find("_global_") != std::string::npos)
						&& (begin == NULL)) {
					begin = git;
				}
				if ((git->getName().str().find("_global_") != std::string::npos)
						&& (begin != NULL)) {
					end = git;
				}
			}
			assert(begin != NULL && end != NULL);
			assert(isa<GlobalVariable>(begin));
			errs() << "begin: " << *begin <<"\n";
			errs() << "end: " << *end <<"\n";

			c = M.getOrInsertFunction("set_global_range",
					llvm::Type::getVoidTy(M.getContext()),
					llvm::Type::getInt8PtrTy(M.getContext()),
					llvm::Type::getInt8PtrTy(M.getContext()),
					llvm::Type::getInt8PtrTy(M.getContext()),
					NULL);
			Function* set_global_range = cast<Function>(c);				

			c = M.getOrInsertFunction("make_table",
					llvm::Type::getVoidTy(M.getContext()),
					llvm::Type::getInt8PtrTy(M.getContext()),
					NULL);
			make_table = cast<Function>(c);				

			value_vec args;
			Instruction* init;
			for (auto &F : M) {
				if (F.getName().str().compare("init") == 0) {
					init = F.begin()->begin();
				}
			}
			// duplicate global vars, and calculate offset!
			GlobalVariable* begin_bak = NULL;
			unsigned pack_counter = 0;
			for (Module::GlobalListType::iterator git = gvars.begin(), 
					ge = gvars.end(); git != ge; ++git) {
				if ((git->getName().str().find("_global_") 
							!= std::string::npos)) {
					GlobalVariable* global_bak = 
						new GlobalVariable(M, 
								git->getType()->getContainedType(0), 
								false, 
								git->getLinkage(), 
								0, 
								git->getName()+"_bak", 
								dyn_cast<GlobalVariable>(begin));
					global_bak->copyAttributesFrom(git);
					global_bak->setSection(".nv_vars");
					global_bak->setAlignment(git->getAlignment());
					global_bak->setInitializer(git->getInitializer());

					if (git == begin) {
						begin_bak = global_bak;
					}
				}
			}

			gv_alloc_ll* iter = ll_head;
			while (true) {
				if (iter->next == NULL) {
					// this is trailing empty space
					// dont add it even if it is not zero
					break;
				}
				else {
					// TODO: THis has bug?!?!?!??!?!?!?
					global_size += iter->size;
					//		errs() << "global size: " << global_size << "\n";
					//		errs() << "iter size: " << iter->size << "\n";
				}
				iter = iter->next;
			}
			//add padding at the end
			//			errs() << "global size: " << global_size << "\n";
			if (global_size % PACK_BYTE != 0)
				global_size += (PACK_BYTE - global_size % PACK_BYTE);
			errs() << "global size: " << global_size << "\n";

			assert(begin_bak != NULL);
			errs() << "begin bak: " << *begin_bak << "\n";
			CastInst* cast = CastInst::CreatePointerCast(begin, Type::getInt8PtrTy(M.getContext()), "", init);
			args.push_back(cast);
			cast = CastInst::CreatePointerCast(end, Type::getInt8PtrTy(M.getContext()), "", init);
			args.push_back(cast);
			cast = CastInst::CreatePointerCast(begin_bak, Type::getInt8PtrTy(M.getContext()), "", init);
			args.push_back(cast);
			CallInst* call = llvm::CallInst::Create(set_global_range, ArrayRef<Value*>(args), "", init);
			// get all globals
			Module::GlobalListType& newGlobalList = M.getGlobalList();
			for (Module::GlobalListType::iterator GI = newGlobalList.begin(); GI != newGlobalList.end(); ++GI){
				// edge case. global var with address is memory-mapped I/O
				// assume that memory-mapped I/O is handled by init() function and do not track
				// also, constant (read-only) should not be cared.
				if (GI->getName().str().find("0x") == std::string::npos
						&& !(GI->isConstant())
						&& GI->getName().str().find("overflow") == std::string::npos
						&& GI->getName().str().find("_global_") != std::string::npos
						&& GI->getName().str().find("_bak") == std::string::npos ) {
					globals.push_back(GI);
				}
			}

#if 1
			//			value_vec writtenGlobal;
			node_vec visitedNode;
			for (auto &F : M) {
				if (F.getName().str() != "init_hw" &&
						// maybe this is unnecessary
						F.getName().str() != "__loop_bound__" &&
						F.getName().str() != "TimerB1_ISR" &&
						F.getName().str() != "init") {
					if (!F.getBasicBlockList().empty()) {
						// iterate the tree from the very start
						//starters.clear();
						//starters.push_back(entryNode);
						while (1) {
							visitedNode.clear();
							bool changed = buildVersioningTree(findNode(&F.getEntryBlock()),
									&visitedNode);
							if (!changed) break;
						}

						visitedNode.clear();
						dynamicVersioning(findNode(&F.getEntryBlock()), &visitedNode);
					}
				}
			}
#endif
			// loop unrolling!!
			for (loop_vec::iterator LI = loops.begin(), LE = loops.end();
					LI != LE; ++LI) {
				// only for tight loop
				if (isTightLoop(*LI)) {
					node_vec preHeaders = (*LI)->getPreHeader();
					for (node_vec::iterator NI = preHeaders.begin(),
							NE = preHeaders.end(); NI != NE; ++NI) {
						Instruction* endI = (*NI)->getBB()->getTerminator();
					}

					// 2) and add init after EVERY checkpoint
					node_vec nodes = (*LI)->getNodes();
					for (node_vec::iterator NI = nodes.begin(), NE = nodes.end();
							NI != NE; ++NI) {
						for(pred_iterator PI = pred_begin((*NI)->getBB());
								PI != pred_end((*NI)->getBB()); ++PI){
							BasicBlock* chkptBB = *PI;
							// only for checkpoint blocks
							if (chkptBB->getName().str().find("newBB") != std::string::npos) {
								// if the checkpoint is not between preheader and header
								BasicBlock* condBB = *pred_begin(chkptBB);
								BasicBlock* prevBB = *pred_begin(condBB);
								if ((*LI)->isMember(prevBB)) {
									Instruction* endI = chkptBB->getTerminator();
								}
							}
						}
					}

					// 3) at loop backedge, increment loopVar
					Node* tail = (*LI)->get_tail();
					assert(tail != NULL);
					Instruction* endI = tail->getBB()->getTerminator();

				}
			}

#if 1 // KIWAN: tight loop optimization disabled
			// deal with the loop handled global vars
			for (loop_vec::iterator LI = loops.begin(), LE = loops.end();
					LI != LE; ++LI) {
				value_vec backedupByLoop = (*LI)->getBackedupByLoop();
				node_vec preHeaders = (*LI)->getPreHeader();
				errs() << "Loop2 in func: " << preHeaders.at(0)->getBB()->getParent()->getName() << "\n";
				for (value_vec::iterator VI = backedupByLoop.begin(),
						VE = backedupByLoop.end(); VI != VE; ++VI) {
					errs() << (*VI)->getName() << "\n";
					// 1) for every preheader, add the guarding check
					for (node_vec::iterator NI = preHeaders.begin(),
							NE = preHeaders.end(); NI != NE; ++NI) {
						Instruction* endI = (*NI)->getBB()->getTerminator();

						// only when it is not there already
						if (!isBackupPresent((*NI)->getBB(), *VI)) {
							CastInst* cast = CastInst::CreatePointerCast(*VI,
									Type::getInt8PtrTy(M.getContext()), "", endI);
							value_vec args;
							args.clear();
							args.push_back(cast);
							CallInst* call = CallInst::Create(check_before_write_must, ArrayRef<Value*>(args), "", endI);
						}
					}

					// 2) and add the backup code after EVERY checkpoint
					// (will this be a win?)
					// But this can be unconditional backup!!
					node_vec nodes = (*LI)->getNodes();
					for (node_vec::iterator NI = nodes.begin(), NE = nodes.end();
							NI != NE; ++NI) {
						for(pred_iterator PI = pred_begin((*NI)->getBB());
								PI != pred_end((*NI)->getBB()); ++PI){
							BasicBlock* chkptBB = *PI;
							// only for checkpoint blocks
							if (chkptBB->getName().str().find("condBB") == std::string::npos) {
								assert(chkptBB->getName().str().find("newBB") != std::string::npos);
								// if the checkpoint is not between preheader and header
								// EDIT: even between preheader and header
								BasicBlock* condBB = *pred_begin(chkptBB);
								BasicBlock* prevBB = *pred_begin(condBB);
								//if ((*LI)->isMember(prevBB)) {
									Instruction* endI = chkptBB->getTerminator();
									CastInst* cast = CastInst::CreatePointerCast(*VI,
											Type::getInt8PtrTy(M.getContext()), "", endI);
									value_vec args;
									args.clear();
									args.push_back(cast);
									CallInst* call = CallInst::Create(check_before_write_must_uc,
											ArrayRef<Value*>(args), "", endI);
								//}
							}
						}
					}
				}
			}
#endif

			//
			// temp check
			for (auto &F : M) {
				for (auto &B: F) {
					for (auto &I : B) {
						if (!isa<AllocaInst>(&I)) {
							for (Value::user_iterator uit = I.user_begin(), ue = I.user_end(); uit != ue; ++uit) {
								Instruction* userInst = dyn_cast<Instruction>(*uit);
								if (I.getParent() != userInst->getParent())
									errs() << "Potential problem: " << I << "\n";
							}
						}
					}
				}
			}


			errs() << "total checkpoint: " << checkpoint_idx << "\n";
			assert(checkpoint_idx == totalCut); // KIWAN: CHKPT DISABLE

			std::vector<Constant*> initializer;
			// add bitmask
			make_global_array(M, 
					Type::getInt8Ty(M.getContext()), 
					(unsigned)((global_size+(PACK_BYTE - 1))/(PACK_BYTE)), 
					new StringRef("backup_bitmask"), NULL, initializer);
			// for sanity check, store global_size to ROM
			Constant* global_size_const = 
				ConstantInt::get(Type::getInt16Ty(M.getContext()), global_size);
			make_global(M, 
					Type::getInt16Ty(M.getContext()),
					*(new Twine("global_size")),
					NULL, 
					global_size_const);

			// mark functions that contains checkpoint with namespace _kw_
			for (auto &F : M) {
				if (!F.getBasicBlockList().empty()) {
					if (isContainingChkpt(&F)) {
						F.setName("_kw_"+F.getName());
						// _kw_ is contagious. Any function that calls _kw_ function
						// is also labeled _kw_
						// Except for main

						for (Value::user_iterator UI = F.user_begin(), UE = F.user_end();
								UI != UE; ++UI) {
							if (CallInst* ci = dyn_cast<CallInst>(*UI)) {
								if (ci->getParent()->getParent()->getName().str().find("_kw_")
										== std::string::npos &&
										ci->getParent()->getParent()->getName().str().find("main")
										== std::string::npos
										) {
									ci->getParent()->getParent()->setName("_kw_"
											+ ci->getParent()->getParent()->getName());
								}
							}
						}
					}
				}
			}
			errs() << "May Alias Points: " << mayAliasCnt << "\n";
			errs() << "Must Alias Var: " << backedUpGV.size() << "\n";
			return true;
		}

		virtual void getAnalysisUsage(AnalysisUsage& AU) const {
			AU.addRequiredID(*taskAnalysisID);
			AU.setPreservesAll();
			AU.addRequired<AAResultsWrapperPass>();
		}

	private:
};

char TransformTask::ID = 3;
RegisterPass<TransformTask> W("transform", "Transform to Alpaca Task");
