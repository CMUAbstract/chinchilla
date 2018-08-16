#include "include/analyzeTool.h"

void readLoopCount(std::vector<unsigned>* loop_count_vec) {
	// read log file
	std::string line;
	std::ifstream log ("./loopcount.log");
	if(log.is_open()){
		while(getline(log, line)){
			loop_count_vec->push_back((unsigned)(atoi(line.c_str())));
		}
	}
	log.close();
}

