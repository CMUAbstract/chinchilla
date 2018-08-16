#include "include/graph.h"
#include "include/analysis.h"
using namespace llvm;
static std::vector<Value*> protectedVals;
unsigned getNodePrice(BasicBlock* bb){
	unsigned price = 0;
	for (BasicBlock::iterator bit = bb->begin(), be = bb->end(); bit != be; ++bit) {
		if (!(isa<AllocaInst>(bit))) {
			price++;
		}
	}	
	return price; //temp
}
unsigned getPenalty(BitVector* out_bit){
	unsigned retval = 0;
	for(unsigned i = 0; i < vals.size(); ++i){
		// check the bitVectors and print dominators
		if(out_bit->test(i)){
			retval++;
		}
	}
	return retval;
}
void Node::print(){
	outs() << "===NODE===\n";
	outs() << "BB: " << *bb << "\n";
	outs() << "Price: " << node_price << "\n";
	outs() << "Out Edges: \n";
	for (std::vector<Edge*>::iterator it = out_edges.begin(); it != out_edges.end(); ++it){
		(*it)->print();
	}
}
void Edge::cut(unsigned& totalPenalty, unsigned& totalCut){
	if (!isCut){
		isCut = true;
		totalPenalty += penalty;
		totalCut += 1;
//		for(unsigned i = 0; i < vals.size(); ++i){
		for(unsigned i = 0; i < vals.size(); ++i){
			// check the bitVectors and print dominators
			if(out_cutVars->test(i)){
				if (std::find(protectedVals.begin(), protectedVals.end(), vals.at(i)) == protectedVals.end())
					protectedVals.push_back(vals.at(i));
			}
		}
	}
}
unsigned Edge::getNumAddedPvar() {
	unsigned result = 0;
	for(unsigned i = 0; i < vals.size(); ++i){
		if(out_cutVars->test(i)){
			if (std::find(protectedVals.begin(), protectedVals.end(), vals.at(i)) == protectedVals.end())
				++result;
		}
	}
	return result;
}


void Node::rmInEdge(Edge* e) {
	if (std::find(in_edges.begin(), in_edges.end(), e) == in_edges.end()) {
		// let's program decently so that this never happens
		assert(false);
	}
	in_edges.erase(std::find(in_edges.begin(), in_edges.end(), e));
}
void Node::rmOutEdge(Edge* e) {
	if (std::find(out_edges.begin(), out_edges.end(), e) == out_edges.end()) {
		// let's program decently so that this never happens
		assert(false);
	}
	out_edges.erase(std::find(out_edges.begin(), out_edges.end(), e));
}
void Node::addInEdge(Edge* e) {
	if (std::find(in_edges.begin(), in_edges.end(), e) != in_edges.end()) {
		// let's program decently so that this never happens
		assert(false);
	}
	if (e->getDest() != this) {
		// let's program decently so that this never happens
		assert(false);
	}
	in_edges.push_back(e);
}
void Node::addOutEdge(Edge* e) {
	if (std::find(out_edges.begin(), out_edges.end(), e) != out_edges.end()) {
		// let's program decently so that this never happens
		assert(false);
	}
	if (e->getSrc() != this) {
		// let's program decently so that this never happens
		assert(false);
	}
	out_edges.push_back(e);
}


//bool Node::isPred(Instruction* I){
//	if (inst == I)
//		return true;
//	for (std::vector<Edge*>::iterator it = in_edges.begin(), e = in_edges.end(); it != e; ++it){
//		if (!((*it)->getIsBackEdge() || (*it)->checkIsCut())){
//			Node* pred = (*it)->getSrc();
//			if(pred->isPred(I))
//				return true;
//		}
//	}
//	return false;
//}
// this does not make copy 
#if 0
void Node::addInEdge(std::vector<Edge*> _in_edge) {
	for (std::vector<Edge*>::iterator it = _in_edge.begin(), e = _in_edge.end(); it != e; ++it){
		//	Edge* edge = new Edge(*it);
		//	edge->setSrc(this);
		if ((*it)->getDest() == this){
			if (std::find(in_edges.begin(), in_edges.end(), *it) == in_edges.end())
				in_edges.push_back(*it);
		}
	}
}
void Node::removeOutEdge(Edge* edge) {
	for (std::vector<Edge*>::iterator it = out_edges.begin(), e = out_edges.end(); it != e; ++it){
		if (*it == edge){
			out_edges.erase(it);
			return;
		}
	}
	errs() << "remove fail!!\n";
}
// this makes copy
std::vector<Edge*> Node::addOutEdge(std::vector<Edge*> _out_edge) {
	std::vector<Edge*> new_out_edge;
	for (std::vector<Edge*>::iterator it = _out_edge.begin(), e = _out_edge.end(); it != e; ++it){
		Edge* edge = new Edge(*it);
		edge->setSrc(this);
		new_out_edge.push_back(edge);
		if (std::find(out_edges.begin(), out_edges.end(), edge) == out_edges.end())
			out_edges.push_back(edge);
	}
	return new_out_edge;
}
// this does not make copy 
void Node::addSingleInEdge(Edge* _in_edge) {
	if (_in_edge->getDest() == this){ //sanity check
		if (std::find(in_edges.begin(), in_edges.end(), _in_edge) == in_edges.end())
			in_edges.push_back(_in_edge);
	}
}
// this makes copy, single edge
Edge* Node::addSingleOutEdge(Edge* _out_edge) {
	Edge* edge = new Edge(_out_edge);
	edge->setSrc(this);
	if (std::find(out_edges.begin(), out_edges.end(), edge) == out_edges.end())
		out_edges.push_back(edge);
	return edge;
}
// this makes no copy, single edge
void Node::addSingleOutEdgeNoCopy(Edge* _out_edge) {
	if (_out_edge->getSrc() == this){ //sanity check
		if (std::find(out_edges.begin(), out_edges.end(), _out_edge) == out_edges.end())
			out_edges.push_back(_out_edge);
	}
}
void Node::removeInEdge(Edge* edge) {
	for (std::vector<Edge*>::iterator it = in_edges.begin(), e = in_edges.end(); it != e; ++it){
		if (*it == edge)
			in_edges.erase(it);
	}
}
#endif
