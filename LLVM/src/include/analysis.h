#ifndef __ANALYSIS__
#define __ANALYSIS__

#include "graph.h"
#include "global.h"
#include "liveVarAnalysis.h"
using namespace llvm;
//extern Analysis *a;
// list of variables
extern std::vector<Value*> vals;
extern std::vector<BasicBlock*> visitedBb;
extern std::map<Function*, Analysis*> liveVarResult;

extern bool savedFirstNode;
extern Node* entryNode;
extern std::vector<MyLoop*> loops;
extern std::vector<Node*> allNode;
extern char* taskAnalysisID;
extern Node* findNode(BasicBlock* bb);
extern void printTree(Node* node);
extern std::vector<Node*> printed;
extern std::map<BasicBlock*, BasicBlock*> callRetMap;
extern std::map<BasicBlock*, Function*> callFuncMap;
extern std::map<BasicBlock*, Function*> retFuncMap;
extern unsigned totalCut;
extern MyLoop* isInTightLoop(Node* n);
extern bool isTightLoop(MyLoop* loop);

extern value_vec alwaysConstVars;
extern value_vec alwaysConstLVs;
#endif
