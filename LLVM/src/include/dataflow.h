#ifndef __CLASSICAL_DATAFLOW_H__
#define __CLASSICAL_DATAFLOW_H__

#include "global.h"
#include <stdio.h>
#include <iostream>
#include <queue>
#include <vector>

#include "available-support.h"

namespace llvm {
	
	typedef BitVector* (*transfer)(Instruction*, BitVector*);
	class Analysis {
	public:
		// use template to cover Expression and Value in one function
		template <class T>
		// constructor
		//Analysis(Function* F, std::vector<T> input_domain, bool init_in_b, bool init_out_b, bool isMeetUnion_, bool isForward_, transfer transfer_func_){
		Analysis();
		template <class T>
		// constructor
		//Analysis(Function* F, std::vector<T> input_domain, bool init_in_b, bool init_out_b, bool isMeetUnion_, bool isForward_, transfer transfer_func_){
		Analysis(Function* F, std::vector<T> input_domain, BitVector* init_in_b, BitVector* init_out_b, bool isMeetUnion_, bool isForward_, transfer transfer_func_){
			init_bit_vector<T>(input_domain, init_in_b, init_out_b);
			init_basic_blocks(F);
			isMeetUnion = isMeetUnion_;
			isForward = isForward_;
			transfer_func = transfer_func_;
			changed = 0;
			startBlock = (F->begin()); // always go forward order (visit order does not matter)
			while(true){ //loop until no change
				visited.clear();
				runAnalysis(startBlock);
				if(!changed)
					break;
				else
					changed = 0;
			}
			outs() << "\n\n";
	//		if (std::is_same<T, BasicBlock*>::value)
	//			print_result_dom<T>(F, input_domain); //print result
	//		else
	//			print_result<T>(F, input_domain); //print result	
		}
		BitVector* get_outVector(Instruction* I){
			BitVector* out_bit = (basicBlocks[I->getParent()])[I].out;
			return out_bit;
		}
		BitVector* get_inVector(Instruction* I){
			BitVector* in_bit = (basicBlocks[I->getParent()])[I].in;
			return in_bit;
		}
	private:
		BasicBlock* startBlock; //start block
		bool changed; // if change has made in current iteration
		transfer transfer_func; //transfer function
		bool isMeetUnion; // 1: union, 0: intersection
		bool isForward = true; // forward or backward analysis
		BitVector* init_in; // in[b]'s initial value
		BitVector* init_out; // out[b]'s initial value
		struct inOut{ //structure that stores info for each instruction (print is done instruction-wise so instead of BB, stores info instruction-wise)
			BitVector* in;
			BitVector* out;
			// this three is only for phi optimization
			bool isPhi = false;
			std::map<BasicBlock*, BitVector*> in_phi;
			std::map<BasicBlock*, BitVector*> out_phi;
		};
		std::vector<BasicBlock*> visited; //mark visited nodes
		std::map<BasicBlock*, std::map<Instruction*, inOut>> basicBlocks; //for each basic block, write down instruction and informations
		// initialize bitVectors
		template <class T>
		void init_bit_vector(std::vector<T> input_domain, BitVector* init_in_b, BitVector* init_out_b){
			init_in = new BitVector(*init_in_b);
			init_out = new BitVector(*init_out_b);
//			init_in = new BitVector(input_domain.size());
//			if(init_in_b)
//				init_in->set();
//			init_out = new BitVector(input_domain.size());
//			if(init_out_b)
//				init_out->set();
		}
		// initialize basicBlocks map
		void init_basic_blocks(Function* F);
		void runAnalysis(BasicBlock* curBb);
		BitVector* meet(BasicBlock* curBb);
		// print result cleanly
		template <class T>
		void print_result_dom(Function* F, std::vector<T> input_domain){
			for(Function::iterator it = F->begin(); it != F->end(); ++it){
				for(BasicBlock::iterator it2 = it->begin(); it2 != it->end(); ++it2){
					if((it)->getTerminator() == it2){
						BitVector* out_bit = (basicBlocks[it])[it2].out;
						for(unsigned i = 0; i < input_domain.size(); ++i){
							if(out_bit->test(i)){
								outs() << (input_domain.at(i))->getName() << " dom ";
								outs() << it->getName() << "\n";
							}
								//outs() << (dyn_cast<BasicBlock>(input_domain.at[i]))->getName() << " dom ";
						}
						
					}
				} 
			}
		}
		template <class T>
		void print_result(Function* F, std::vector<T> input_domain){
			for(Function::iterator it = F->begin(); it != F->end(); ++it){
				for(BasicBlock::iterator it2 = it->begin(); it2 != it->end(); ++it2){
					std::vector<T> in_vec;
					BitVector* in_bit = (basicBlocks[it])[it2].in;
					for(unsigned i = 0; i < input_domain.size(); ++i){
						if(in_bit->test(i))
							in_vec.push_back(input_domain.at(i)); // look at bitVecotrs and make vector for printing IN
					}
					if(!dyn_cast<PHINode>(it2)) //print IN only when it is not PHI Node
						printSet(&in_vec);
					outs() << *it2 << "\n"; // print instruction itself
					std::vector<T> out_vec;
					BitVector* out_bit = (basicBlocks[it])[it2].out;
					for(unsigned i = 0; i < input_domain.size(); ++i){
						if(out_bit->test(i))
							out_vec.push_back(input_domain.at(i)); // look at bitVectors and make vector for printing OUT
					}
					if(it2 == --(it->end())){ // prev OUT and cur IN is the same so only print INs except for last instruction
						if(!dyn_cast<PHINode>(it2)) // don't print for PHI node. but BB and never end with phi node anyways
							printSet(&out_vec);
						outs() << "\n";
					}
				}
			} 
		}
	}; 

}

#endif
