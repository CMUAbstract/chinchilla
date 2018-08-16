#include "include/liveVarSplit.h"

typedef std::map<Instruction*, unsigned> i_u_map;
typedef std::vector<BasicBlock*> bb_vec;

value_vec lvs_vals;
std::map<Function*, Analysis*> lvs_liveVarResult;
Instruction* begin_inst;
bb_vec visited;

class LiveVarSplit : public ModulePass {
	public:
		static char ID;
		std::vector<unsigned> loop_count_vec;
		LiveVarSplit() : ModulePass(ID) { }

		unsigned label = 1;
		
		bool check_val_in_bv(BitVector* bv, Value* v) {
			// TODO: this sucks. if it is slow, make it faster
			unsigned j = 0;
			for (value_vec::iterator VI = lvs_vals.begin(), VE = lvs_vals.end(); VI != VE; ++VI, ++j) {
				if ((*VI) == v) {
					return bv->test(j);
				}
			}
			assert(false);
		}

		bool check_connected(Instruction* src, Instruction* dst, Value* val) {
			BasicBlock* src_block = src->getParent();
			BasicBlock::iterator BI = BasicBlock::iterator(src);
			bool result = false;

			if (!check_val_in_bv(lvs_liveVarResult[src_block->getParent()]->get_inVector(BI), val)) return false;

			if (src == dst) return true; //TODO: check.
			
			while (cast<Instruction>(BI) != &(src_block->back())) {
				// if search meets begin again, break
				if (begin_inst == BI) return false;
				if (!check_val_in_bv(lvs_liveVarResult[src_block->getParent()]->get_outVector(BI), val)) return false;
				++BI;
				// step through and see if it is connected to dest or not
				if (cast<Instruction>(BI) == dst) return true;
			}

			if (!check_val_in_bv(lvs_liveVarResult[src_block->getParent()]->get_outVector(BI), val)) return false;

			for (succ_iterator SI = succ_begin(src_block); SI != succ_end(src_block); ++SI){
				if (std::find(visited.begin(), visited.end(), *SI) == visited.end()) {
					// if at least one is connected, it is connected
					visited.push_back(*SI);
					result |= check_connected(&((*SI)->front()), dst, val);
				}
			}
			return result;
		}

		void label_vars(i_u_map* var_label_map, Value* val) {
			errs() << "var " << val->getName() << "\n";
			for (i_u_map::iterator MI = var_label_map->begin(), ME = var_label_map->end(); MI != ME; ++MI) {
				// for unlabeled vals
				if (isa<StoreInst>(MI->first) && (*MI).second == 0) {
					// pick one and label it
					// search should always start from store
					(*MI).second = label;
					for (i_u_map::iterator MI2 = var_label_map->begin(), ME2 = var_label_map->end(); MI2 != ME2; ++MI2) {
						// for unlabeled vals
						if (isa<LoadInst>(MI2->first) && (*MI2).second == 0) {
							// dest is always load
							// Hacky way of dealing loops.
							// When the search reaches the instruction right beform source,
							// return
							begin_inst = MI->first;
							BasicBlock::iterator search_begin = BasicBlock::iterator(MI->first);
							search_begin++;
							visited.clear();
							bool connected = check_connected(dyn_cast<Instruction>(search_begin), MI2->first, val);

							// search both ways
							begin_inst = MI2->first;
							search_begin = BasicBlock::iterator(MI2->first);
							search_begin++;
							visited.clear();
							connected |= check_connected(dyn_cast<Instruction>(search_begin), MI->first, val);
							if (connected) {
								(*MI2).second = label;
								errs() << *(MI->first) << " and " << *(MI2->first) << " connected\n";
							}
							else {
								errs() << *(MI->first) << " and " << *(MI2->first) << " not connected\n";

							}
						}
					}
					label++;
				}
			}

			// sanity check
			for (i_u_map::iterator MI = var_label_map->begin(), ME = var_label_map->end(); MI != ME; ++MI) {
				if (MI->second == 0) {
					errs() << *(MI->first) << "\n";
					errs() << (MI->first)->mayWriteToMemory() << "\n";
					errs() << (MI->first)->mayReadFromMemory() << "\n";
					assert(false && "some did not get labeled!\n");
					// TODO: some gets here. It is pointers. Do conservatively.
					// TODO: Dealing with ptr is hard. maybe discard it for now. It can be future opt
					// Problem.
					// p = &a;
					// a = 3
					// b = *p
					// ==chkpt
					// c = a
					// ==chkpt
					// a = 4
					// b = *p
					// c = a
					//
					// we might want to make a local in second case
					// but can't because of p
					//
					//
					//
					//
					// TODO: Deal with Function calls
				}
			}
		}

		void split_and_rename(Value* val) {
			i_u_map var_label_map;
			label = 1;
			for (Value::user_iterator UI = val->user_begin(), UE = val->user_end(); UI != UE; ++UI) {
				if (Instruction* user = dyn_cast<Instruction>(*UI)) {
					var_label_map[user] = 0;
				}
				else {
					errs() <<  *(*UI) << "\n";
					assert(false);
				}
			}
			label_vars(&var_label_map, val);
			errs() << "value: " << val->getName() << " split: " << label - 1 << "\n";
		}

		virtual bool runOnModule(Module& M) {
			lva_vals = &lvs_vals;
			callerPass = this;
			lva_liveVarResults = &lvs_liveVarResult;
			analyzeLiveVar(M);

			for (value_vec::iterator VI = lvs_vals.begin(), VE = lvs_vals.end(); VI != VE; ++VI) {
				split_and_rename(*VI);
			}
			while(1);
			return true;
		}

		virtual void getAnalysisUsage(AnalysisUsage& AU) const {
			AU.setPreservesAll();
			AU.addRequired<AAResultsWrapperPass>();
			//AliasAnalysis::getAnalysisUsage(AU);
		}
	private:
};

char LiveVarSplit::ID = 5;
RegisterPass<LiveVarSplit> LVS("livevarsplit", "live var split");
