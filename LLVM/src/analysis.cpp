#include "include/analysis.h"

using namespace llvm;
//#define BUDGET 200000
#define BUDGET 500
#define LARGE 500000
#define TIGHT_LOOP_THRES 6

enum {
	NO_CUT_NEEDED,
	CUT_NEEDED,
	ALREADY_CUT,
};

// change this to 1 if you want to put checkpoint on every block
#define FINE_CUT 1

std::map<BasicBlock*, BasicBlock*> callRetMap;
std::map<BasicBlock*, Function*> callFuncMap;
std::map<BasicBlock*, Function*> retFuncMap;
std::map<Function*, Analysis*> liveVarResult;
// list of variables
std::vector<Value*> vals;
std::vector<BasicBlock*> visitedBb;
// map of function and its alias anlysis
std::map<Function*, AliasAnalysis*> aliasMap;
bool savedFirstNode = false;
Node* entryNode;
loop_vec loops;
node_vec allNode;
unsigned totalPenalty = 0;
unsigned totalCut = 0;
value_vec alwaysConstVars;
value_vec alwaysConstLVs;

// transfer function
Node* findNode(BasicBlock* bb){
	for (node_vec::iterator it = allNode.begin(), e = allNode.end(); 
			it != e; ++it){
		if ((*it)->getBB() == bb)
			return (*it);
	}
	assert(false);
	return NULL;
}


// this first analyze loop size, and
// 1. break back edge if loop size is too large, or
// 1-1. undetermined (implement later)
// 1-2. If back edge is broken, node price is as normal,
// 1-3. but edge penalty is multiplied by loopcount
// 2. If loop size is within power budget,
// 2-1. edge penalty is multiplied by loopcount, and
// 2-2. node price is also multiplied by loopcount
// 3. Analyze from outmost loop to inwards
// 3-1. On nested loop, edge penalty is multiplied by mult of all nested loopcount
// 3-2. node price is mult'd by all nested loopcount except those loops who are broekn by 1.
void analyzeLoop(Module& M) {
	// find back edges
	for (loop_vec::iterator it = loops.begin(); it != loops.end(); ++it) {
		(*it)->markBackEdges();
	}
	// first, size edge penalty and node price
#if 0
	while (true) {
		bool changed = false;
		for (loop_vec::iterator it = loops.begin(); it != loops.end(); ++it) {
			if (!((*it)->isSizeSet())) {
				// my turn to get analyzed!
				(*it)->setNodePrice();
				changed = true;
			}
		}
		if (!changed)
			break;
	}
	// now, analyze the size
	while (true) {
		bool changed = false;
		for(loop_vec::iterator it = loops.begin(); it != loops.end(); ++it){
			if (!((*it)->isAnalyzed()) && ((*it)->isParentAnalyzed())){
				// my turn to get analyzed!
				if ((*it)->get_loopcount() == 0) {
					outs() << "loop size unknown, always cut!\n";
					(*it)->cutBackEdges(totalPenalty, totalCut);
				}
				else if ((*it)->getLoopSize() > BUDGET){
					outs() << "loop too large!\n";
					errs() << "loopsize: " << (*it)->getLoopSize() << "\n";
					(*it)->shrinkNodePrice();
					errs() << "shrinked loopsize: " << (*it)->getLoopSize() << "\n";

					(*it)->cutBackEdges(totalPenalty, totalCut);
				}
				else{
					outs() << "loop not too large!\n";
					errs() << "loopsize: " << (*it)->getLoopSize() << "\n";
				}
				(*it)->analyzeDone();
				changed = true;
			}
		}
		if (!changed)
			break;
	}
#endif // KIWAN: we do not need this anymore!!
}
node_vec startNode;

node_vec doneStartNode;

// the return value
// 0: no cut needed starting from this node
// 1: cut needed, sending cutCandidate
// 2: I will cut. Do not cut further and simply re-call me (when non-dominated node or large function call is encountered
//    in this case don't forget to push_back newStart
unsigned findCuttablePortion(Node* curNode, edge_vec* cutCandidate, unsigned price, Node* firstNode){
	price += curNode->getPrice();
	if (price > BUDGET){ // current path needs cut
		return CUT_NEEDED;
	}
	else{
		edge_vec out_edges = curNode->getOutEdges();
		for (edge_vec::iterator it = out_edges.begin(), e = out_edges.end(); it != e; ++it) {
//			if (!((*it)->getIsBackEdge())) { // only do for non-back edge
				if (!((*it)->checkIsCut()) && (*it)->getEdgePenalty() < MAX) { // check if the edge is already cut or not cuttable
					cutCandidate->push_back(*it);
#if FINE_CUT == 1
					return CUT_NEEDED;
#endif
					unsigned needCut = findCuttablePortion((*it)->getDest(), cutCandidate, price, firstNode);
					if (needCut == CUT_NEEDED) return CUT_NEEDED;
					else if (needCut == ALREADY_CUT) return ALREADY_CUT;
					else {
						if (cutCandidate->at(cutCandidate->size() - 1) == *it) { // pop cur edge from cutCandidate. We will go back to where there was branch and inspect other branch
							cutCandidate->erase(cutCandidate->begin() + cutCandidate->size() - 1);
						}
						else {
							assert(false);
						}
					}
				}
				else {
					if (std::find(doneStartNode.begin(), doneStartNode.end(), (*it)->getDest()) == doneStartNode.end())
						// maybe we never reach here
						startNode.push_back((*it)->getDest());
				}

			//}
		}

		// if control reaches here, there is no need to cut
		return NO_CUT_NEEDED;
	}
}

// cut penalty is not only the penalty of the node
// rather, you should cut all the edges that is incoming to the cutted edge->dest
// (for single entry)
// so that is the real penalty that must be considered
Node* randomCut(edge_vec* cutCandidate) {
#if FINE_CUT == 1
	assert(cutCandidate->size() == 1);
	for (edge_vec::iterator it = cutCandidate->begin(), e = cutCandidate->end(); it != e; ++it){
		if ((*it)->getEdgePenalty() == MAX) {
			startNode.erase(std::find(startNode.begin(), startNode.end(), (*it)->getSrc()));
			return (*it)->getDest();
		}
	}
#endif
	// random cut inversely proportional to penalty
	// Also let us prefer cut near the power budget
	unsigned const w0 = 5;
	unsigned const w1 = 10 - w0; //weight

	double sum_of_penalty = 0;
	double sum_of_count = 0;
	double count = 0;

	double penalty;

	double sum_of_penalty_square = 0;
	double sum_of_count_square = 0;
	for (edge_vec::iterator it = cutCandidate->begin(), e = cutCandidate->end(); it != e; ++it){
		penalty = 0;
		count += (*it)->getSrc()->getPrice();

		// when cutting edge, you should either cut all the incoming edge to that dest,
		// or duplicate the code (future work)	
		//edge_vec in_edge = (*it)->getDest()->getInEdges();
		//for (edge_vec::iterator iit = in_edge.begin(), ie = in_edge.end(); iit != ie; ++iit) {
		penalty += (*it)->getNumAddedPvar();
		//}
		sum_of_penalty += penalty;
		sum_of_penalty_square += penalty*penalty;
		sum_of_count += (*it)->getSrc()->getPrice();
		sum_of_count_square += ((*it)->getSrc()->getPrice())*((*it)->getSrc()->getPrice());
	}
	// there are two important thing. Count and penalty. Penalty is lower the better.
	// So we use the score of (-penalty).
	// Since usually count >> penalty, we normalize
	double mean_count = sum_of_count / cutCandidate->size();
	double mean_penalty = sum_of_penalty / cutCandidate->size();
	double stddev_count = sum_of_count_square / cutCandidate->size() - mean_count*mean_count; 
	double stddev_penalty = sum_of_penalty_square / cutCandidate->size() - mean_penalty*mean_penalty; 

	Edge* best_edge = NULL;
	count = 0;
	double best_score = -1;
	for (edge_vec::iterator it = cutCandidate->begin(), e = cutCandidate->end(); it != e; ++it){
		penalty = 0;
		count += (*it)->getSrc()->getPrice();
		//		errs() << "cut candidate: " << (*it)->getDest()->getBB()->getName() << "\n";
		// when cutting edge, you should either cut all the incoming edge to that dest,
		// or duplicate the code (future work)	
		//edge_vec in_edge = (*it)->getDest()->getInEdges();
		//for (edge_vec::iterator iit = in_edge.begin(), ie = in_edge.end(); iit != ie; ++iit) {
		//	penalty += (*iit)->getNumAddedPvar();
		//}
		penalty += (*it)->getNumAddedPvar();
		double norm_count = stddev_count == 0 ? 1 : (count - mean_count) / stddev_count;
		double norm_penalty = stddev_penalty == 0 ? 1 : (penalty - mean_penalty) / stddev_penalty;
		double score = ((double) ((w0 * (-1*norm_penalty) + w1 * (norm_count)))) /((double) (((*it)->getLoopMultiplier()))); // currently linear. maybe square or exp?
		if (score > best_score) {
			best_score = score;
			best_edge = (*it);
		}
	}
	//errs() << "best edge: " << best_edge->getSrc()->getBB()->getName() << "--->" << best_edge->getDest()->getBB()->getName() << "\n";

	assert(best_edge != NULL);
	best_edge->cut(totalPenalty, totalCut);
	//	edge_vec in_edge = best_edge->getDest()->getInEdges();
	//	for (edge_vec::iterator it2 = in_edge.begin(), e2 = in_edge.end(); it2 != e2; ++it2){ // when cutting, cut all the in_edges to out
	//		if (!((*it2)->checkIsCut()))
	//			(*it2)->cut(totalPenalty, totalCut);
	//	}
	//outs() << "cut in: ";
	//best_edge->print();
	//while (1);
	return best_edge->getDest();
}

void cutGraph(){
	edge_vec cutCandidate;
	while (true){
		if (startNode.size() == 0)
			break;
		Node* firstNode = startNode.at(0);
		visitedBb.clear();

		unsigned needCut = findCuttablePortion(firstNode, &cutCandidate, 0, firstNode);
		//for (edge_vec::iterator it = cutCandidate.begin(), e = cutCandidate.end(); it != e; ++it){
		//	errs() << ((*it)->getSrc()->getBB()->getName()) << "\n";
		//}
		if (needCut == NO_CUT_NEEDED){
			//	cutCandidate.clear();
			// errs() << "node erase: " << *(firstNode->getInst()) << "\n";
			doneStartNode.push_back(firstNode);
			startNode.erase(startNode.begin());
		}
		else if (needCut == CUT_NEEDED) {
			assert(cutCandidate.size() != 0);
			Node* newFirst = randomCut(&cutCandidate);
			if (std::find(doneStartNode.begin(), doneStartNode.end(), newFirst) == doneStartNode.end())
				startNode.push_back(newFirst);
		}
		else { //already cutted by findCuttablePortion

		}
		// if the node is not dominated by firstNode, cut!
		cutCandidate.clear();
	}
}

class TaskAnalysis : public ModulePass {
	public:
		static char ID;
		std::vector<unsigned> loop_count_vec;
		TaskAnalysis() : ModulePass(ID) { }
		std::vector<BasicBlock*> returnStack;

		std::vector<BasicBlock*> lr_stack;
		node_vec cur_func_call_head;
		std::map<Node*, Node*> func_call_head_tail;

		bool isProtectStart(Node* cur_node) {
			bool isStart = false;
			BasicBlock* B = cur_node->getBB();
			std::vector<CallInst*> needRemove;

			for (auto &I: *B) {
				if (CallInst* ci = dyn_cast<CallInst>(&I)) {
					if (ci->getCalledFunction() == NULL) {
					}
					else if (ci->getCalledFunction()->getName().str().find("no_chkpt_start")
						 	!= std::string::npos) {
						isStart = true;
						needRemove.push_back(ci);
					}
				}
			}
			for (std::vector<CallInst*>::iterator it = needRemove.begin(), e = needRemove.end(); it != e; ++it) {
				(*it)->eraseFromParent();
			}
			return isStart;
		}

		bool isProtectEnd(Node* cur_node) {
			bool isStart = false;
			BasicBlock* B = cur_node->getBB();
			std::vector<CallInst*> needRemove;

			for (auto &I: *B) {
				if (CallInst* ci = dyn_cast<CallInst>(&I)) {
					if (ci->getCalledFunction() == NULL) {
					}
					else if (ci->getCalledFunction()->getName().str().find("no_chkpt_end")
						 	!= std::string::npos) {
						isStart = true;
						needRemove.push_back(ci);
					}
				}
			}
			for (std::vector<CallInst*>::iterator it = needRemove.begin(), e = needRemove.end(); it != e; ++it) {
				(*it)->eraseFromParent();
			}
			return isStart;
		}

		void buildTree(Module& M, Node* cur_node, bool isProtected){
			// TODO: naive impl. THere might be edge cases
			// Currently this will be enough
			if (isProtectStart(cur_node)) {
				assert(isProtected == 0);
				isProtected = 1;
			}
			if (isProtectEnd(cur_node)) {
				assert(isProtected == 1);
				isProtected = 0;
			}
			BasicBlock* block = cur_node->getBB();
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(*(block->getParent())).getLoopInfo();	
			///
			// currently we assume loopcount is always known.
			// If it is not the case, we should conservatively always cut the back edge
			// However, even in that case we cannot decide what is the cost of each edge inside the loop
			// maybe conservatively we can set it to super-high
			unsigned loopcount = 1;
			bool loopHeader = false;
			MyLoop* curLoop = NULL; // current loop. NULL if it is not inside loop
			if (Loop* loop = LI.getLoopFor(block)) {
				// check if MyLoop instance for this loop already exists
				// since header dominates the loop, always header gets passed first.
				// register loop when header is encountered.
				if (LI.isLoopHeader(block)) {
					//		loopHeader = true;

					LLVMContext& C = block->getContext();
					MDNode* N = MDNode::get(C, MDString::get(C, std::to_string(loops.size())));
					N->replaceOperandWith(0, N);
					loop->setLoopID(N);
				}
				for (loop_vec::iterator it = loops.begin(); it != loops.end(); ++it) {
					if (((*it)->getLoopID()) == loop->getLoopID()){
						curLoop = *it;
					}
				}
				loopcount = loop_count_vec.at(0);
				//	if (loopcount == 0) loopcount = LARGE; //heuristic
				loop_count_vec.erase(loop_count_vec.begin());

				// for some reason, for the second time the outermost loop header creates new loop..
				// prevent it from the second time
				if (curLoop == NULL){
					loopHeader = true;
					outs() << "new loop!!" << loopcount << "\n";
					//assert(loopcount != 0);
					curLoop = new MyLoop(loop, loop->getLoopID(), loopcount);
					outs() << *loop << "\n";
					loops.push_back(curLoop);
					if (Loop* parent = loop->getParentLoop()){
						outs() << "I have parent loop\n";
						while(true){
							for (loop_vec::iterator it = loops.begin(); it != loops.end(); ++it){
								if (((*it)->getLoopID()) == parent->getLoopID()){
									curLoop->add_parent(*it);
								}
							}
							if (!(parent = parent->getParentLoop())){
								break;
							}
						}
					}
				}
				assert(curLoop != NULL);

				curLoop->add_node(cur_node);
				curLoop->add_node_to_parents(cur_node);
				if(loopHeader){
					curLoop->set_head(cur_node); //set loop header
					//	edge->cut(totalPenalty, totalCut);
					loopHeader = false;
				}
			}
			visitedBb.push_back(block);
			// if it is return (Not main but no successor)
#if 0
			if (succ_begin(block) == succ_end(block) && block->getParent()->getName().str().find("main") == std::string::npos) {
				if (!isa<ReturnInst>(block->getTerminator())) {
					// program exit (ex - exit(0)). Do nothing
				}
				else {
					assert(lr_stack.size() != 0);
					BasicBlock* succ = lr_stack.back();
					lr_stack.pop_back();
					Node* func_head = cur_func_call_head.back();
					cur_func_call_head.pop_back();

					// save head-tail relation for this function call
					assert(func_call_head_tail.find(func_head) == func_call_head_tail.end());
					func_call_head_tail[func_head] = cur_node;
					errs() << "stack pop: " << *succ << "\n";

					retFuncMap[block] = block->getParent();
					BasicBlock* predBB = *(pred_begin(succ));
					// when succ is never visited
					if (std::find(visitedBb.begin(), visitedBb.end(), succ) == visitedBb.end()){
						Node* new_cur = new Node(succ);
						Edge* edge = new Edge(cur_node, new_cur, liveVarResult[succ->getParent()]->get_inVector(succ->getFirstNonPHI()), liveVarResult[succ->getParent()]->get_outVector(predBB->getTerminator()));
						edge->cut(totalPenalty, totalCut);
						cur_node->addOutEdge(edge);
						new_cur->addInEdge(edge);

						buildTree(M, new_cur);
					}
					else {
						Node* new_cur = findNode(succ);
						Edge* edge = new Edge(cur_node, new_cur, liveVarResult[succ->getParent()]->get_inVector(succ->getFirstNonPHI()), liveVarResult[succ->getParent()]->get_outVector(predBB->getTerminator()));
						edge->cut(totalPenalty, totalCut);
						cur_node->addOutEdge(edge);
						new_cur->addInEdge(edge);
					}
				}
			}
#endif
			for(succ_iterator SI = succ_begin(block); SI != succ_end(block); ++SI){
				BasicBlock* succ = *SI;

				// if bb and succ of bb does not have name, it must only contain callInst
#if 0
				if (!(succ->hasName()) && !(succ_begin(succ)->hasName())) {
					errs() << "call func\n";
					CallInst* callInst = dyn_cast<CallInst>(&(succ->front()));
					assert(callInst != NULL);
					BasicBlock* newSucc = &(callInst->getCalledFunction()->front()); 

					BasicBlock* succBB = *(succ_begin(succ));
					callRetMap[block] = succBB;
					callFuncMap[block] = newSucc->getParent();
					// when succ is never visited
					if (std::find(visitedBb.begin(), visitedBb.end(), newSucc) == visitedBb.end()){
						Node* new_cur = new Node(newSucc);
						Edge* edge = new Edge(cur_node, new_cur, liveVarResult[succ->getParent()]->get_inVector(succ->getFirstNonPHI()), liveVarResult[succ->getParent()]->get_outVector(block->getTerminator()));
						edge->cut(totalPenalty, totalCut);
						cur_node->addOutEdge(edge);
						new_cur->addInEdge(edge);

						// and it must have single successor
						lr_stack.push_back(succBB);
						cur_func_call_head.push_back(new_cur);
						errs() << "stack push: " << *succBB << "\n";
						buildTree(M, new_cur);
					}
					else {
						Node* new_cur = findNode(newSucc);
						Edge* edge = new Edge(cur_node, new_cur, liveVarResult[succ->getParent()]->get_inVector(succ->getFirstNonPHI()), liveVarResult[succ->getParent()]->get_outVector(block->getTerminator()));
						edge->cut(totalPenalty, totalCut);
						cur_node->addOutEdge(edge);
						new_cur->addInEdge(edge);

						// jump directly to return block
						// TODO: fix here!!! gonna be hard..!!
						// How to fix: add another map, and save entry - exit basicblock pair and search
						Node* new_cur_ret = new Node(succBB); // this can never have been visited!
						// get the tail of the function
						Node* tail_node = findNode(func_call_head_tail[new_cur]->getBB());
						assert(tail_node != NULL);
						edge = new Edge(tail_node, new_cur_ret, liveVarResult[succ->getParent()]->get_inVector(succBB->getFirstNonPHI()), liveVarResult[succ->getParent()]->get_outVector(succ->getTerminator()));
						edge->cut(totalPenalty, totalCut);
						tail_node->addOutEdge(edge);
						new_cur_ret->addInEdge(edge);
						buildTree(M, new_cur_ret);
					}
				}
				else { 
#endif
					// when succ is never visited
					if (std::find(visitedBb.begin(), visitedBb.end(), succ) 
							== visitedBb.end()){
						Node* new_cur = new Node(succ);
						Edge* edge;
						if (isProtected) {
							edge = new Edge(cur_node, 
									new_cur);
						}
						else {
							edge = new Edge(cur_node, 
									new_cur, 
									liveVarResult[succ->getParent()]);
						}
						cur_node->addOutEdge(edge);
						new_cur->addInEdge(edge);
						buildTree(M, new_cur, isProtected);
					}
					else {
						Node* new_cur = findNode(succ);
						Edge* edge;
						if (isProtected) {
							edge = new Edge(cur_node, 
									new_cur);
						}
						else {
							edge = new Edge(cur_node, 
									new_cur, 
									liveVarResult[succ->getParent()]);
						}
						cur_node->addOutEdge(edge);
						new_cur->addInEdge(edge);
					}
					//				}
			}
			errs() << "hit leaf: returning\n";
		}
		void calcDoms(Node* firstNode){
			unsigned vbsize = allNode.size();
			BitVector* out_prev = new BitVector(vbsize);
			out_prev->reset();
			bool changed = false;
			node_vec visited;
			unsigned i = 0;
			while (true){
				i++;
				visited.clear();
				changed = traverseDom(firstNode, out_prev, &visited);
				if (!changed)
					break;
			}
		}
		bool traverseDom(Node* node, BitVector* out_prev, node_vec* visited){
			BitVector* out_cur = new BitVector(*out_prev); 
			unsigned j = 0;
			for (node_vec::iterator it = allNode.begin(), 
					e = allNode.end(); it != e; ++it, ++j){
				if(*it == node){
					out_cur->set(j);
				}
			}
			bool changed = node->setDoms(out_cur);
			//	errs() << "Node: " << *(node->getInst()) << "\n";
			//	node->printDom();
			visited->push_back(node);
			edge_vec succ = node->getOutEdges();
			for (edge_vec::iterator it = succ.begin(), e = succ.end(); it != e; ++it){
				Node* sucNode = (*it)->getDest();
				edge_vec prev = sucNode->getInEdges();
				for (edge_vec::iterator it2 = prev.begin(), 
						e2 = prev.end(); it2 != e2; ++it2){
					BitVector* bv = (*it2)->getSrc()->getDoms();
					if(bv != NULL){
						*(out_cur) &= *(bv);
					}
				}
				if (std::find(visited->begin(), visited->end(), sucNode) 
						== visited->end())
					changed |= traverseDom(sucNode, out_cur, visited);
			}
			return changed;
		}

		AliasAnalysis* getAA(Function* F) {
			return &(this->getAnalysis<AAResultsWrapperPass>(*F).getAAResults());
		}

		void eraseAnnotation(Module& M) {
			std::vector<CallInst*> toBeRemoved;
			for (auto &F : M) {
				for (auto &B : F) {
					for (auto &I : B) {
						if (CallInst* ci = dyn_cast<CallInst>(&I)) {
							if (ci->getCalledFunction() == NULL) {
							}
							else if (ci->getCalledFunction()->getName().str().find("__loop_bound") != std::string::npos) {
								toBeRemoved.push_back(ci);
							}
						}
					}
				}
			}
			for (std::vector<CallInst*>::iterator it = toBeRemoved.begin(), e = toBeRemoved.end(); it != e; ++it) {
				(*it)->eraseFromParent();
			}
		}
		virtual bool runOnModule(Module& M) {
			// first, remove all anotation
			eraseAnnotation(M);
			srand(time(NULL));
			readLoopCount(&loop_count_vec);

			// live var analysis
			// hacky way..
			lva_vals = &vals;
			callerPass = this;
			lva_liveVarResults = &liveVarResult;
			findAllVars(M);
			analyzeLiveVar(M);

			// Optimization: these filter out vars that does not needs
			// protecting
			alwaysConstVars = analyzeConstant(M);
			alwaysConstLVs = analyzeConstLocalVar(M);

			//Function* main = M.getFunction("main");
			for (auto &F : M) {
				// do not analyze external functions
				if (!F.getBasicBlockList().empty()) {
					// do not analyze these!
					if (F.getName().str() != "init_hw" &&
							// maybe this is unnecessary
							F.getName().str() != "__loop_bound__" &&
							F.getName().str() != "TimerB1_ISR" &&
							F.getName().str() != "init") {
						visitedBb.clear();
						//Node* cur_node = new Node(&(main->getEntryBlock()));
						Node* cur_node = new Node(&(F.getEntryBlock()));
						entryNode = cur_node;
						buildTree(M, cur_node, 0);
						analyzeLoop(M);
						errs() << "analyze loop done\n";
						calcDoms(cur_node);
						errs() << "calc dom done\n";
						//cutLoopHeader();
						//printLoops();
						startNode.push_back(cur_node);
						errs() << "start cutting!\n";
						cutGraph();
					}
				}
			}

			errs() << "Total Cut: " << totalCut << "\n";

			// Did not modify the incoming Function.
			return false;
		}

		virtual void getAnalysisUsage(AnalysisUsage& AU) const {
			AU.setPreservesAll();
			AU.addRequired<AAResultsWrapperPass>();
			//AliasAnalysis::getAnalysisUsage(AU);
			AU.addRequired<LoopInfoWrapperPass>();
			AU.addRequired<ScalarEvolutionWrapperPass>();
		}

	private:
};


/*
 * @brief Check if the loop is a tight loop
 * Loop is tight if:
 * 1) No function call inside
 * 2) Node num smaller than TIGHT_LOOP_THRES
 * 3) No nested loop inside
 * This is just a heurisitics!
 */
bool isTightLoop(MyLoop* loop) {
	if (loop->containsCall()) {
		return false;
	}
	else if (loop->isNested()) {
		return false;
	}
	else if (loop->getNumNodes() > TIGHT_LOOP_THRES) {
		return false;
	}
	else {
		return true;
	}
}

/*
 * @brief Check if the node is contained by a small loop
 * and return the loop, otherwise return NULL.
 * Loop is tight if:
 * 1) No function call inside
 * 2) Node num smaller than TIGHT_LOOP_THRES
 * 3) No nested loop inside
 * This is just a heurisitics!
 */
MyLoop* isInTightLoop(Node* n) {
	loop_vec containingLoops;
	for (loop_vec::iterator it = loops.begin(); it != loops.end(); ++it) {
		if ((*it)->isMember(n)) {
			containingLoops.push_back(*it);
		}
	}

	loop_vec candidateLoops;
	for (loop_vec::iterator it = containingLoops.begin(); it != containingLoops.end(); ++it) {
		if ((*it)->containsCall()) {
		}
		else if ((*it)->isNested()) {
		}
		else if ((*it)->getNumNodes() > TIGHT_LOOP_THRES) {
		}
		else {
			candidateLoops.push_back(*it);
		}
	}

	if (candidateLoops.size() == 0) {
		return NULL;
	}
	assert(candidateLoops.size() == 1);
	return candidateLoops.at(0);
}

char TaskAnalysis::ID = 1;
char* taskAnalysisID = &TaskAnalysis::ID;
RegisterPass<TaskAnalysis> Y("taskanalysis", "Analysis for Alpaca");
