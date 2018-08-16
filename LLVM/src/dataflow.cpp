// 15-745 S16 Assignment 2: dataflow.cpp
// Group: Kiwan, Jay-yoon
////////////////////////////////////////////////////////////////////////////////

#include "llvm/IR/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "include/dataflow.h"
namespace llvm {
	// for each BB, init in and out bitVectors for every instructions to specified init value
	void Analysis::init_basic_blocks(Function* F){
		for (Function::iterator it = F->begin(); it != F->end(); ++it){
			if(basicBlocks.find(it) == basicBlocks.end()){
				std::map<Instruction*, inOut> insts;
				for (BasicBlock::iterator it2 = it->begin(); it2 != it->end(); ++it2){
					inOut in_out;
					in_out.in = new BitVector(*init_in);
					in_out.out = new BitVector(*init_out);
					insts[it2] = in_out; 
				}
				basicBlocks[it] = insts;
			}
		}
	}
	// iteratively run analysis
	void Analysis::runAnalysis(BasicBlock* curBb){
		visited.push_back(curBb);
		if(isForward){ //forward analysis
			BitVector* in = meet(curBb); //meet
			for (BasicBlock::iterator it = curBb->begin(); it != curBb->end(); ++it){
				BitVector* result = transfer_func(it, in); //apply transfer function
				(basicBlocks[curBb])[it].in = in;
				if(*((basicBlocks[curBb])[it].out) != *result){
					(basicBlocks[curBb])[it].out = result;
					changed = 1; // check if results has changed
				}
				in = result;
			}
		}
		else{ //backward analysis
			BitVector* out = meet(curBb);
			std::map<BasicBlock*, BitVector*> out_phi; // in and out is different for each pred bb when there are phi node
			std::map<BasicBlock*, BitVector*> result_phi; // same as above
			BasicBlock::iterator it = curBb->end();
//			errs() << "B: " << *curBb << "\n";
			while (true) { //using while since reverse_iterator is buggy
				--it;
				Instruction* I = it;
//				errs() << "II: " << *(I) << "\n
				PHINode* phi;
				// backward analysis gets complicated because of phi node. We want to make phi node transparent to transfer function programming
				if(!(phi = dyn_cast<PHINode>(I))){ //if not phi node, easy
					BitVector* result = transfer_func(I, out); // apply transfer function
					(basicBlocks[curBb])[I].out = out;
					if(*((basicBlocks[curBb])[I].in) != *result){
						(basicBlocks[curBb])[I].in = result;
						changed = 1; //check if changed
					}
					out = result;
				}
				else{ //when phi node
					std::vector<BasicBlock*> pred_of_phi;
					for(PHINode::block_iterator bit = phi->block_begin(); bit != phi->block_end(); ++bit){
						pred_of_phi.push_back(*bit);
					}
					for(std::vector<BasicBlock*>::iterator bit = pred_of_phi.begin(); bit != pred_of_phi.end(); ++bit){ // loop for every predecessor of phi node
						// hacky trick is being used. to calculate different in and out bitVector for different preds of phi,
						// we make a phi node who only has that specific pred and use it to calculate bitVector
						// after calculating we restore the phi nodes
						PHINode* newPhi = PHINode::Create(phi->getType(), phi->getNumIncomingValues()-1, "", I);
						std::vector<BasicBlock*> detach;
						// detach other bbs than that of current interest
						for(std::vector<BasicBlock*>::iterator bit2 = pred_of_phi.begin(); bit2 != pred_of_phi.end(); ++bit2){
							if(bit != bit2){
								detach.push_back(*bit2);
							}
						}
						// save the detached values in newPhi
						for(std::vector<BasicBlock*>::iterator dit = detach.begin(); dit != detach.end(); ++dit)
							newPhi->addIncoming(phi->removeIncomingValue(*dit), *dit);
						// using the modified phi node, calculate result for different preds.
						if(out_phi.size() == 0){
							result_phi[*(bit)] = transfer_func(phi, out);
							if((basicBlocks[curBb])[I].in_phi.find(*(bit)) == (basicBlocks[curBb])[I].in_phi.end()){
								changed = 1;
							}
							else if(*((basicBlocks[curBb])[I].in_phi[*(bit)]) != *result_phi[*(bit)]){
								changed = 1;
							}
						}
						else{
							result_phi[*(bit)] = transfer_func(phi, out_phi[*(bit)]);
							if((basicBlocks[curBb])[I].in_phi.find(*(bit)) == (basicBlocks[curBb])[I].in_phi.end()){
								changed = 1;
							}
							else if(*((basicBlocks[curBb])[I].in_phi[*(bit)]) != *result_phi[*(bit)]){
								changed = 1;
							}
						}
						// restore phi node. newPhi gets erased when no nodes are left
						for(std::vector<BasicBlock*>::iterator dit = detach.begin(); dit != detach.end(); ++dit)
							phi->addIncoming(newPhi->removeIncomingValue(*dit), *dit);
					}
					(basicBlocks[curBb])[I].out = out;
					// set isPhi to true for phi instructions
					(basicBlocks[curBb])[I].isPhi = true;
					(basicBlocks[curBb])[I].out_phi = out_phi;
					(basicBlocks[curBb])[I].in_phi = result_phi;
					out_phi = result_phi;
				}
				if (it == curBb->begin()) {
					break;
				}
			}
		}
		// do depth-first search until finishes. The order shouldn't affect correctness.
		for(succ_iterator SI = succ_begin(curBb); SI != succ_end(curBb); ++SI){
			BasicBlock* succ = *SI;
			if(std::find(visited.begin(), visited.end(), succ) == visited.end()){
				runAnalysis(succ);
			}
		}
	} 
	// meet operation
	BitVector* Analysis::meet(BasicBlock* curBb){
		BitVector* result = new BitVector(init_in->size());
		// set initial value
		if(isMeetUnion)
			result->reset();
		else
			result->set();
		if(isForward){ //forward analysis
			if(curBb == startBlock) //if first block, consider out[entry]
				if(isMeetUnion)
					*(result) |= *(init_in);
				else
					*(result) &= *(init_in);
			for(pred_iterator PI = pred_begin(curBb); PI != pred_end(curBb); ++PI){ // otherwise, do meet
				BasicBlock* pred = *PI;
				if(isMeetUnion)
					*(result) |= *((basicBlocks[pred])[pred->getTerminator()].out);
				else
					*(result) &= *((basicBlocks[pred])[pred->getTerminator()].out);
			}
		}
		else{ // backward analysis
			bool hasSuccessor = false;
			for(succ_iterator SI = succ_begin(curBb); SI != succ_end(curBb); ++SI){ // if no successor, consider in[exit]
				hasSuccessor = true;
			}
			if(!hasSuccessor)
				if(isMeetUnion)
					*(result) |= *(init_out);
				else
					*(result) &= *(init_out);
			for(succ_iterator SI = succ_begin(curBb); SI != succ_end(curBb); ++SI){ //otherwise, to meet
				BasicBlock* succ = *SI;
				BitVector* bv_from_succ;
				if((basicBlocks[succ])[succ->begin()].isPhi){ // slightly complicated for phi successor
					bv_from_succ = ((basicBlocks[succ])[succ->begin()].in_phi[curBb]);
				}
				else{
					bv_from_succ = ((basicBlocks[succ])[succ->begin()].in);
				}
				if(isMeetUnion){
					*(result) |= *bv_from_succ;
				}
				else
					*(result) &= *bv_from_succ;
			}
		}	
		return result;
	}
}
