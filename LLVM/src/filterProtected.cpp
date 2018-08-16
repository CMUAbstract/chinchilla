#include "include/filterProtected.h"
#include "include/analysis.h"
/*
 *	We filter out globals that need not be protected here
 */

bool isConstant(Value* v) {
	if (std::find(alwaysConstVars.begin(), alwaysConstVars.end(), v)
			!= alwaysConstVars.end()) {
		return true;
	}
	return false;
}

bool isConstLocalVar(Value* v) {
	if (std::find(alwaysConstLVs.begin(), alwaysConstLVs.end(), v)
			!= alwaysConstLVs.end()) {
		return true;
	}
	return false;
}

bool needsProtection(Value* v) {
	// If the value only always holds
	// same constant value
	if (isConstant(v)) {
		errs() << "constant: " << v->getName() << "\n";
		return false;
	}
	if (isConstLocalVar(v)) {
		errs() << "constant local: " << v->getName() << "\n";
//		if (v->getName().str().find("classModel.addr") != std::string::npos) {
		if (v->getName().str().find("arr") != std::string::npos) {
			errs() << v->getName() << "\n";
			while(1);
		}
		return false;
	}
	return true;
}
