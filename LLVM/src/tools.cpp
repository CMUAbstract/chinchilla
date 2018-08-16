#include "include/tools.h"
gv_alloc_ll* ll_head = NULL;

bool isContainingCall(BasicBlock* bb) {
	for (auto &I : *bb) {
		if (CallInst* ci = dyn_cast<CallInst>(&I)) {
			Function* calledF = ci->getCalledFunction();
			if (!calledF) {
				// if null: unknown function
				return true;
			}
			// make whitelist for some known function
			if (calledF->getName().str().find("check_before_write")
					== std::string::npos &&
					calledF->getName().str().find("llvm.dbg.declare")
					== std::string::npos
					) {
				// Single-block function is not considered call
				if (calledF->getBasicBlockList().size() == 1) {
					// unless it calls another function that contains call
					bool callFuncContainingCall = false;
					for (auto &BB : *calledF) {
						callFuncContainingCall |= isContainingCall(&BB);
					}
					if (callFuncContainingCall) {
						return true;
					}
				}
				else {
					return true;
				}
			}
		}
	}
	return false;
}

bool isMemcpy(Instruction* I) {
	if (CallInst* ci = dyn_cast<CallInst>(I)) {
		Function* calledF = ci->getCalledFunction();
		if (calledF) {
			if (calledF->getName().str().find("llvm.memcpy") != std::string::npos) {
				return true;
			}
		}
	}
	return false;
}


// returns size of a type (assuming allocation is being helpful)
unsigned get_size(Type* type, Module* M) {
	unsigned result = M->getDataLayout().getTypeSizeInBits(type)/8;
	if (result == 0) result = 1;
	return result;
}

void make_global_array(Module& M, Type* type, unsigned size, StringRef* name, GlobalVariable* insert_before, ArrayRef<Constant*> initializer) {
	// declare chkpt_book
	GlobalVariable* arr;
	if (insert_before) {
		arr = new GlobalVariable(M, ArrayType::get(type, size), false, GlobalValue::ExternalLinkage, 0, llvm::Twine(*name), insert_before); 
	}
	else {
		arr = new GlobalVariable(M, ArrayType::get(type, size), false, GlobalValue::ExternalLinkage, 0, llvm::Twine(*name)); 
	}
	arr->setAlignment(2);
	arr->setSection(".nv_vars");
	// initialize as zero
	// Empty means zero
	Constant* init_arr = ConstantArray::get(ArrayType::get(type, size), initializer);
	arr->setInitializer(init_arr);	
}

GlobalVariable* make_global(Module& M, Type* type, Twine name, GlobalVariable* insert_before, Constant* initializer) {
	// declare chkpt_book
	GlobalVariable* arr;
	if (insert_before) {
		arr = new GlobalVariable(M, type, false, GlobalValue::ExternalLinkage, 0, name, insert_before); 
	}
	else {
		arr = new GlobalVariable(M, type, false, GlobalValue::ExternalLinkage, 0, name); 
	}
	arr->setAlignment(2);
	arr->setSection(".nv_vars");
	// initialize as zero
	// Empty means zero
	arr->setInitializer(initializer);	
	return arr;
}

GlobalVariable* make_global_volatile(Module& M, Type* type, StringRef* name, GlobalVariable* insert_before, Constant* initializer) {
	// declare chkpt_book
	GlobalVariable* arr;
	if (insert_before) {
		arr = new GlobalVariable(M, type, false, GlobalValue::ExternalLinkage, 0, llvm::Twine(*name), insert_before); 
	}
	else {
		arr = new GlobalVariable(M, type, false, GlobalValue::ExternalLinkage, 0, llvm::Twine(*name)); 
	}
	arr->setAlignment(2);
	// initialize as zero
	// Empty means zero
	arr->setInitializer(initializer);	
	return arr;
}
// make + pack
GlobalVariable* make_global_considering_layout(Module& M, Type* type, 
		Twine name, Constant* initializer) {
	unsigned target_size = get_size(type, &M);
	assert(target_size != 0);
	bool allocated = false;
	GlobalVariable* gVar;

	gv_alloc_ll* iter = ll_head;
	gv_alloc_ll* new_ll = new gv_alloc_ll();
	/*
	 * if size is larger than 4, alignment must be at least 4.
	 * (Assuming largest val in the struct is 4 and within struct
	 * the compiler give a good alignment)
	 * if size is 3 or 2, alignment 2 should be given.
	 * if size is 1 alignment can be 1	
	 */
	errs() << "allocating " << name << "\n";
	errs() << "size " << target_size << "\n";
	unsigned align = target_size >= 4 ? 4 : target_size >= 2 ? 2: 1;
	while (iter) {
		if (iter->gvar == NULL && iter->size > 0) {
			errs() << "iter size " << iter->size << "\n";
			errs() << "accum size " << iter->prev->accum_size << "\n";
			// there is an empty space we might fiddle in
			assert(iter->prev->accum_size != 0);
			unsigned space_needed = (iter->prev->accum_size % align) + target_size;
			if (iter->size >= space_needed) {
				// this is large enough
				// if not perfectly fits
				if (iter->prev->accum_size % align == 0) {
					// if you can simply position the new gv right after the prev
					// (ll) -> (new_ll) -> (empty) -> (ll)
					if (iter->next == NULL) {
						gVar = new GlobalVariable(M, type, false, 
								GlobalValue::ExternalLinkage, initializer, 
								(name));
					}
					else {
						gVar = new GlobalVariable(M, type, false, 
								GlobalValue::ExternalLinkage, initializer, 
								(name), iter->next->gvar);
					}
					gVar->setSection(".nv_vars");
					gVar->setAlignment(align);

					new_ll->gvar = gVar;
					new_ll->size = target_size;
					new_ll->accum_size = iter->prev->accum_size + target_size;
					new_ll->next = iter;
					new_ll->prev = iter->prev;
					new_ll->is_pack_begin = false;

					iter->prev->next = new_ll;

					iter->size = iter->size - target_size;
					iter->prev = new_ll;

					allocated = true;
					break;
				}
				else {
					// if you need some trailing space for alignment
					// (ll) -> (new empty) -> (new ll) -> (ll)
					if (iter->next == NULL) {
						gVar = new GlobalVariable(M, type, false, 
								GlobalValue::ExternalLinkage, initializer, 
								(name));
					}
					else {
						gVar = new GlobalVariable(M, type, false, 
								GlobalValue::ExternalLinkage, initializer, 
								(name), iter->next->gvar);
					}
					gVar->setSection(".nv_vars");
					gVar->setAlignment(align);

					gv_alloc_ll* new_empty_ll = new gv_alloc_ll();
					new_empty_ll->gvar = NULL;
					new_empty_ll->size = iter->prev->accum_size % align;
					new_empty_ll->accum_size = iter->prev->accum_size +
						new_empty_ll->size;
					new_empty_ll->next = new_ll;
					new_empty_ll->prev = iter->prev;
					new_empty_ll->is_pack_begin = false;

					new_ll->gvar = gVar;
					new_ll->size = target_size;
					new_ll->accum_size = new_empty_ll->accum_size + 
						target_size;
					new_ll->next = iter;
					new_ll->prev = new_empty_ll;
					new_ll->is_pack_begin = false;

					iter->prev->next = new_empty_ll;

					iter->size = iter->size - target_size - new_empty_ll->size;
					iter->prev = new_ll;

					allocated = true;
					break;
				}
			}
		}
		if (iter->next == NULL) {
			// if this is the last ll, 
			// break;
			break;
		}
		iter = iter->next;
	}

	if (!allocated) {
		gVar = new GlobalVariable(M, type, false, GlobalValue::ExternalLinkage, 
				initializer, (name));
		gVar->setSection(".nv_vars");
		// we start fresh
		gVar->setAlignment(PACK_BYTE);

		gv_alloc_ll* ll = new gv_alloc_ll();
		ll->gvar = gVar;
		if (target_size <= PACK_BYTE) {
			ll->size = target_size;
			ll->accum_size = target_size;
		}
		else {
			// fake sizing
			if (target_size % PACK_BYTE != 0) {
				ll->size = target_size + (PACK_BYTE - target_size % PACK_BYTE);
			}
			else {
				ll->size = target_size;
			}
			//ll->size = target_size + (PACK_BYTE - target_size % PACK_BYTE);
			ll->accum_size = PACK_BYTE;
		}
		ll->next = NULL;
		ll->prev = NULL;
		ll->is_pack_begin = true;

		// this indicate how many empty space is left in current pack
		gv_alloc_ll* empty_ll = new gv_alloc_ll();
		empty_ll->gvar = NULL;
		if (target_size <= PACK_BYTE) {
			empty_ll->size = PACK_BYTE - target_size;
		}
		else {
			empty_ll->size = 0;
		}
		empty_ll->accum_size = PACK_BYTE;
		empty_ll->next = NULL;
		empty_ll->prev = ll;
		empty_ll->is_pack_begin = false;

		ll->next = empty_ll;
		if (iter) {
			assert(iter->gvar == NULL);
			// this is not the first
			//if we couldn't allocate succesfully, 
			//we start a new pack
			ll->prev = iter;
			iter->next = ll;
		}
		else {
			assert(ll_head == NULL);
			ll_head = ll;
		}
	}

	return gVar;

#if 0



	Module::GlobalListType& gvars = M.getGlobalList();
	for (Module::GlobalListType::iterator git = gvars.begin(), ge = gvars.end(); git != ge; ++git) {
		// only do it for the vars not already packed
		if ((git->getName().str().find("_global_") != std::string::npos)) {
			unsigned size = get_size(git->getType()->getContainedType(0), &M);
			if (pack + size <= PACK_BYTE) {
				pack += size;
				if (pack == PACK_BYTE) {
					pack = 0;
				}
			}
			// if pack is 0, it means size of git is really large (larget than PACK_BYTE) we discard trailing space in that case
			else if (pack != 0) {
				// here, there is a dead space
				// Try fitting it
				errs() << "dead space is occurring..pack is " << pack << " and size is " << target_size << "\n";
				if (pack + target_size <= PACK_BYTE) {
					errs() << "I might fit in!!..\n";
					// insert it here
					gVar = new GlobalVariable(M, type, false, GlobalValue::ExternalLinkage, initializer, (name), git);
					gVar->setAlignment(size);
					gVar->setSection(".nv_vars");
					return gVar;
				}
				pack = 0;
			}
		}
	}
	// insert at the end
	// 1. there is no space that it can fit in before,
	//    but it can fit in nicely at the end
	// 2. it cannot fit into any place including the end
	//    we pad the remaining part and start new
	gVar = new GlobalVariable(M, type, false, GlobalValue::ExternalLinkage, initializer, (name));
	gVar->setSection(".nv_vars");
	if (pack + target_size <= PACK_BYTE) {
		if (pack != 0) {
			// 1. it fits nicely
			gVar->setAlignment(size);
			return gVar;
		}
	}
	// we start fresh
	gVar->setAlignment(PACK_BYTE);
	return gVar;
#endif
}

/*
 * @brief check if the function contains
 * checkpoint
 */
bool isContainingChkpt(Function* F) {
	if (F->getName().str() != "main" &&
			F->getName().str() != "init_hw" &&
			F->getName().str() != "__loop_bound__" &&
			F->getName().str() != "TimerB1_ISR" &&
			F->getName().str() != "init") {
		if (F->getBasicBlockList().size() > 1) {
			return true;
		}
	}
	return false;
}
