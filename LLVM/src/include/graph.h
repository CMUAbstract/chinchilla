#ifndef __GRAPH__
#define __GRAPH__

#include "dataflow.h"
#include "global.h"
#include "tools.h"

#define MAX 65535

class Edge;
class Node;
class MyLoop;

using namespace llvm;

typedef std::vector<Node*> node_vec;
typedef std::vector<Edge*> edge_vec;
typedef std::vector<MyLoop*> loop_vec;

extern node_vec allNode;
unsigned getNodePrice(BasicBlock* bb);
unsigned getPenalty(BitVector* outVector);


class Node {
	public:
		Node(BasicBlock* _bb){
			bb = _bb;
			node_price = getNodePrice(bb);
			out_edges.clear();
			in_edges.clear();
			doms = NULL;
			versionBitmask = NULL;
			allNode.push_back(this);
			mother = _bb->getParent();
		}
		BitVector* getVersionBitmask() {
			return versionBitmask;
		}
		void initVersionBitmask(unsigned size) {
			versionBitmask = new BitVector(size);
		}
		void setVersionBitmask(unsigned idx) {
			versionBitmask->set(idx);
		}
		BasicBlock* getBB(){
			return bb;
		}
		void setBB(BasicBlock* _bb){
			bb = _bb;
		}
		void clearOutEdge() {
			out_edges.clear();
		}
		void clearInEdge() {
			in_edges.clear();
		}
		std::vector<Edge*> getOutEdges() const{
			return out_edges;
		}
		std::vector<Edge*> getInEdges() const{
			return in_edges;
		}
		unsigned getPrice() const{
			return node_price;
		}
		void setPrice(unsigned price){
			node_price = price;
		}
		void print();
		bool setDoms(BitVector* bv){
			if (doms != NULL && *bv == *doms)
				return false;
			else{
				BitVector* bv2 = new BitVector(*bv);
				doms = bv2;
			}
			return true;
		}
		BitVector* getDoms(){
			return doms;
		}
		bool isDom(unsigned j){
			return doms->test(j);
		}
		void printDom(){
			for (unsigned i = 0; i < doms->size(); ++i){
				if (i % 5 == 0)
					errs() << " ";
				errs() << doms->test(i);
			}
			errs() << "\n";
		}
		void addInEdge(Edge* e);
		void addOutEdge(Edge* e);
		void rmInEdge(Edge* e);
		void rmOutEdge(Edge* e);
		Function* getMother() {
			return mother;
		}
		bool containsCall() {
			return isContainingCall(bb);
		}
	private:
		std::vector<Edge*> out_edges;
		std::vector<Edge*> in_edges;
		unsigned node_price;
		BasicBlock* bb;
		BitVector* doms;
		Function* mother;
		BitVector* versionBitmask;
		//std::vector<Edge*> done_out_edges;
		//bool renamed;
		//bool doneTrans;
};

class Edge {
	public:
		Edge(Node* s, Node* d){ // this is kinda hacky, but this edge never becomes cut
			src = s;
			dest = d;
			penalty = MAX;
			isCut = false;
			isBackEdge = false;
			in_cutVars = NULL;
			out_cutVars = NULL;
			loopMultiplier = MAX;
		}
		Edge(Node* s, Node* d, Analysis* a){
			loopMultiplier = 1;
			src = s;
			dest = d;
			if (a != NULL)
				penalty = (s == NULL)? 0 : getPenalty(a->get_outVector(s->getBB()->getTerminator()));
			else
				penalty = 0;
			isCut = false;
//			isCut = true;
			isBackEdge = false;
			if (a != NULL) {
				out_cutVars = (s == NULL)? NULL : a->get_outVector(s->getBB()->getTerminator());
				//in_cutVars = (d == NULL)? NULL : a->get_inVector(&(d->getBB()->front()));
				in_cutVars = (d == NULL)? NULL : a->get_inVector((d->getBB()->getFirstNonPHI()));
			}
			else {
				in_cutVars = NULL;
				out_cutVars = NULL;
			}
		}
		// special case used for function call
		Edge(Node* s, Node* d, BitVector* inVector, BitVector* outVector){
			loopMultiplier = 1;
			src = s;
			dest = d;
			penalty = (s == NULL)? 0 : getPenalty(outVector);
			isCut = false;
			//isCut = true;
			isBackEdge = false;
			out_cutVars = (s == NULL)? NULL : outVector;
			//in_cutVars = (d == NULL)? NULL : a->get_inVector(&(d->getBB()->front()));
			in_cutVars = (d == NULL)? NULL : inVector;
		}
		Edge(Edge* e){
			loopMultiplier = e->getLoopMultiplier();
			src = e->getSrc();
			dest = e->getDest();
			penalty = e->getEdgePenalty();
			isCut = e->checkIsCut();
			isBackEdge = e->getIsBackEdge();
			in_cutVars = e->getInCutVars();
			out_cutVars = e->getOutCutVars();
		}
		unsigned getLoopMultiplier() {
			return loopMultiplier;
		}
		unsigned setLoopMultiplier(unsigned n) {
			loopMultiplier = n;
		}
		void print(){
			outs() << "===EDGE===\n";
			if (dest->getBB() == NULL){
				outs() << "dest: NULL" << "\n";	
			}
			else{
				outs() << "dest: " << dest->getBB()->getName() << "\n";
			}
			outs() << "penalty: " << penalty << "\n";
			outs() << "cut: " << isCut << "\n";
		}
		Node* getSrc(){
			return src;
		}
		Node* getDest(){
			return dest;
		}
		void setSrc(Node* n){
			src = n;
		}
		void setDest(Node* n){
			dest = n;
		}
		void cut(unsigned& totalPenalty, unsigned& totalCut);
		unsigned getEdgePenalty(){
			return penalty;
		}
		void setEdgePenalty(unsigned pen){
			penalty = pen;
		}
		bool checkIsCut() const {
			return isCut;
		}
		void markBackEdge(bool _isBackEdge){
			isBackEdge = _isBackEdge;
		}
		bool getIsBackEdge() const {
			return isBackEdge;
		}
		BitVector* getInCutVars(){
			return in_cutVars;
		}
		BitVector* getOutCutVars(){
			return out_cutVars;
		}
		unsigned getNumAddedPvar();
	private:
		Node* src;
		Node* dest;
		unsigned penalty;
		unsigned loopMultiplier;
		bool isBackEdge;
		bool isCut;
		BitVector* in_cutVars;
		BitVector* out_cutVars;
};

class MyLoop {
	public:
		MyLoop(Loop *_loop, MDNode* _loopid, unsigned _loopcount){
			loop = _loop;
			nodes.clear();
			head = NULL;
			tail = NULL;
			loopid = _loopid;
			loopcount = _loopcount;
			analyzed = false;
			broken = false;
			setSize = false;
			simpleLoop = false;
		}
		bool isSimpleLoop() {
			return simpleLoop;
		}
		void setSimpleLoop(bool _simpleLoop) {
			simpleLoop = _simpleLoop;
		}
		void analyzeDone(){
			analyzed = true;
		}
		bool isAnalyzed(){
			return analyzed;
		}
		void add_node(Node* n){
			nodes.push_back(n);
		}
		void add_node_to_parents(Node* n){
			for (std::vector<MyLoop*>::iterator it = parentLoops.begin(); it != parentLoops.end(); ++it){
				(*it)->add_node(n);
			}
		}
		Loop* getLoop(){
			return loop;
		}
		MDNode* getLoopID(){
			return loopid;
		}
		void setLoopID(MDNode* _loopid){
			loopid = _loopid;
		}
		void set_tail(Node* n){
			tail = n;
		}
		void set_head(Node* n){
			assert(head == NULL);
			head = n;
		}
		Node* get_head(){
			return head;
		}
		Node* get_tail(){
			return tail;
		}
		void print_nodes(){
			for (std::vector<Node*>::iterator it = nodes.begin(); it != nodes.end(); ++it){
				(*it)->print();
			}
		}
		void cutExitBlock(unsigned& totalPenalty, unsigned& totalCut) {
			for (std::vector<Node*>::iterator it = nodes.begin(); it != nodes.end(); ++it){
				std::vector<Edge*> out_edge = (*it)->getOutEdges();
				for (std::vector<Edge*>::iterator it2 = out_edge.begin(), e2 = out_edge.end(); it2 != e2; ++it2) {
					// check if the dest of any node is outside loop
					Node* dest = (*it2)->getDest();
					if (std::find(nodes.begin(), nodes.end(), dest) == nodes.end()) {
						// the dest is outside loop. the edge is an exit!
						(*it2)->cut(totalPenalty, totalCut);
					}
				}
			}
		}
		void add_parent(MyLoop* L){
			if (std::find(parentLoops.begin(), parentLoops.end(), L)
					== parentLoops.end()) {
				parentLoops.push_back(L);
				L->add_child(this);
			}
		}
		void add_child(MyLoop* L) {
			if (std::find(childLoops.begin(), childLoops.end(), L)
					== childLoops.end()) {
				childLoops.push_back(L);
				L->add_parent(this);
			}
		}
		bool isParentAnalyzed(){
			for (std::vector<MyLoop*>::iterator it = parentLoops.begin(); it != parentLoops.end(); ++it){
				if (!((*it)->isAnalyzed())){
					return false;
				}
			}
			return true;
		}
		unsigned get_loopcount(){
			return loopcount;
		}
		void print_parent(){
			for (std::vector<MyLoop*>::iterator it = parentLoops.begin(); it != parentLoops.end(); ++it){
				outs() << "Parent: " << (*it)->getLoopID() << "\n";
			}

		}
		void setNodePrice(){
			if(!setSize){
				if (loopcount != 0) { // if loop size is unknown, don't set price (we will always cut it)
					for (std::vector<Node*>::iterator it = nodes.begin(); it != nodes.end(); ++it){
						(*it)->setPrice((*it)->getPrice() * loopcount);
						// set Edge penalty also
						std::vector<Edge*> out_edge = (*it)->getOutEdges();
						// for every out edge of the node
						for(std::vector<Edge*>::iterator it2 = out_edge.begin(); it2 != out_edge.end(); ++it2){
							// if it is edge inside loop,
							if (isMember((*it2)->getDest())){
								(*it2)->setLoopMultiplier((*it2)->getLoopMultiplier() * loopcount);
//								(*it2)->setEdgePenalty((*it2)->getEdgePenalty() * loopcount);				
							}
						}	

					}
				}
				setSize = true;
			}
		}
		// this only resize node price, not edge penalties, since it is unnecessary
		void shrinkNodePrice(){
			for (std::vector<Node*>::iterator it = nodes.begin(); it != nodes.end(); ++it){
				(*it)->setPrice((*it)->getPrice() / loopcount);
				// set Edge penalty also
			}
		}
		void multNodePrice(unsigned mult){
			for (std::vector<Node*>::iterator it = nodes.begin(); it != nodes.end(); ++it){
				(*it)->setPrice((*it)->getPrice()*mult);
				// set Edge penalty also
			}
		}
		void markBackEdges(){
			bool foundBackEdge = false;
			for (std::vector<Node*>::iterator it = nodes.begin(); it != nodes.end(); ++it){
				std::vector<Edge*> out_edge = (*it)->getOutEdges();
				// for every out edge of the node
				for(std::vector<Edge*>::iterator it2 = out_edge.begin(); it2 != out_edge.end(); ++it2){
					// if edge points to header
					if (isHeader((*it2)->getDest())){
						foundBackEdge = true;
						(*it2)->markBackEdge(true);
						this->set_tail(*it); //set tail
					}
				}

			}
			assert(foundBackEdge);
		}
		void cutBackEdges(unsigned& totalPenalty, unsigned& totalCut){
			for (std::vector<Node*>::iterator it = nodes.begin(); it != nodes.end(); ++it){
				std::vector<Edge*> out_edge = (*it)->getOutEdges();
				// for every out edge of the node
				for(std::vector<Edge*>::iterator it2 = out_edge.begin(); it2 != out_edge.end(); ++it2){
					// if edge points to header
					if (isHeader((*it2)->getDest())){
						// get all in edges of the header
						(*it2)->cut(totalPenalty, totalCut);
					}
				}
			}
			broken = true;

		}
		bool isSizeSet(){
			return setSize;
		}
		unsigned getLoopSize(){
			unsigned result = 0;
			for (std::vector<Node*>::iterator it = nodes.begin(); it != nodes.end(); ++it){
				result += (*it)->getPrice();
			}
			return result;
		}
		bool isHeader(Node* node){
			//			outs() << "NODE: " << (node) << "\n";
			//			(node)->print();
			return ((node) == (head));
		}
		bool isMember(Node* node){
			for (std::vector<Node*>::iterator it = nodes.begin(); it != nodes.end(); ++it){
				if ((*it) == node)
					return true;
			}
			return false;
		}
		bool isMember(BasicBlock* bb){
			for (std::vector<Node*>::iterator it = nodes.begin(); it != nodes.end(); ++it){
				if ((*it)->getBB() == bb)
					return true;
			}
			return false;
		}
		bool isBackEdgeBroken(){
			return broken;
		}
		unsigned getNumNodes() {
			return nodes.size();
		}
		bool containsCall() {
			for (node_vec::iterator NI = nodes.begin(), NE = nodes.end();
					NI != NE; ++NI) {
				if ((*NI)->containsCall()) {
					return true;
				}
			}
			return false;
		}
		bool isNested() {
			if (childLoops.size() != 0) {
				return true;
			}
			else {
				return false;
			}
		}
		node_vec getPreHeader() {
			node_vec preHeaders;
			edge_vec in_edges = head->getInEdges();
			for (edge_vec::iterator EI = in_edges.begin(), EE = in_edges.end();
					EI != EE; ++EI) {
				if (!isMember((*EI)->getSrc())) {
					preHeaders.push_back((*EI)->getSrc());
				}
			}
			assert(preHeaders.size() != 0);
			return preHeaders;
		}
		bool isBackedupByLoop(Value* v) {
			for (value_vec::iterator VI = backedupByLoop.begin(),
					VE = backedupByLoop.end(); VI != VE; ++VI) {
				if ((*VI) == v) {
					return true;
				}
			}
			return false;
		}
		void addBackedupByLoop(Value* v) {
			if (isBackedupByLoop(v)) {
				return;
			}
			else {
				backedupByLoop.push_back(v);
			}
		}
		value_vec getBackedupByLoop() {
			return backedupByLoop;
		}
		node_vec getNodes() {
			return nodes;
		}
	private:
		std::vector<MyLoop*> parentLoops;
		std::vector<MyLoop*> childLoops;
		std::vector<Node*> nodes;
		Node* head;
		Node* tail;
		MDNode* loopid;
		Loop *loop;
		unsigned loopcount;
		bool analyzed;
		bool broken;
		bool setSize;
		bool simpleLoop;
		value_vec backedupByLoop;
};
#endif
