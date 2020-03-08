#include "Liveness.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/ilist_node.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Type.h"

#include <map>
#include <set>
#include <list>
#include <utility>
#include <algorithm>
#include <iterator>

#include <fstream>
#include <iostream>

using namespace llvm;
using namespace std;



namespace {
		// Liveness - The first implementation, without getAnalysisUsage.
		struct Liveness : public FunctionPass {
				string func_name = "test";
				static char ID; // Pass identification, replacement for typeid
				Liveness() : FunctionPass(ID) {}
				//vincent build a map for UE/VK, key: BB, value: live var/killed
				map<BasicBlock*, set<llvm::StringRef>> UE;
				map<BasicBlock*, set<llvm::StringRef>> VK;
				map<BasicBlock*, set<llvm::StringRef>>::iterator it;
				map<BasicBlock*, set<llvm::StringRef>>::iterator kit;

				map<BasicBlock*, set<llvm::StringRef>> LO; // init
				map<BasicBlock*, set<llvm::StringRef>>::iterator lit;
				std::list<BasicBlock*> workList;


				//vincent create file for output
				ofstream createOutput(Function &F){  
						string file = F.getParent() ->getSourceFileName();
						int index = file.find(".");
						file =file.substr(0,index);
						string c = ".out";
						file.append(c);
						ofstream pathOut;
						pathOut.open(file, std::ios::out | std::ios::app);
						return pathOut;
				}

				auto computeUEandVarKill(Function &F,set<StringRef> UEVar, set<StringRef> VarKill, BasicBlock &BB ){


						for (Instruction &inst : BB) {
								//vincent UEVar are on the right part of the statement and load operation code is 31. 
								if (inst.getOpcode() == 31){
										StringRef var_name = inst.getOperand(0)->getName();
										kit = VK.find(&BB);
										//var_name not in VK
										if (kit->second.find(var_name) != kit->second.end()) continue;
										// put var_name into UEVar
										it = UE.find(&BB);
										UEVar = it->second;
										UEVar.insert(var_name);
										UE.erase(it);
										UE.insert(std::pair<BasicBlock*, std::set<llvm::StringRef>>(&BB,UEVar));
								}

								//vincent VarKill are in the left part of the statement
								if (inst.getOpcode() == 32) {
										StringRef var_kill = inst.getOperand(1)->getName();
										// put var_kill into Varkill
										kit = VK.find(&BB);
										VarKill = kit->second;
										VarKill.insert(var_kill);
										VK.erase(kit);
										VK.insert(std::pair<BasicBlock*, std::set<llvm::StringRef>>(&BB,VarKill));
								}
						}
				}

				auto computeLiveOut(Function &F, map<BasicBlock*, set<llvm::StringRef>> UE,
								map<BasicBlock*, set<llvm::StringRef>> VK){

						for (BasicBlock &BB : F) {
								set<StringRef> LIVEOUT;
								LO.insert(std::pair<BasicBlock*, std::set<llvm::StringRef>>(&BB,LIVEOUT));
								workList.push_back(&BB);
						}
						while (!workList.empty()) {
								BasicBlock* tmp = workList.front();// BB
								workList.pop_front();
								map<BasicBlock*, set<llvm::StringRef>>::iterator it; 
								it = LO.find(tmp);
								set<llvm::StringRef> originLIVEOUT = it->second;// original LIVEOUT
								// compute liveOut
								const auto *TInst = tmp->getTerminator();
								set<llvm::StringRef> resultSet;// result LIVEOUT
								for (int i = 0, NSucc = TInst->getNumSuccessors(); i < NSucc; i++) {
										BasicBlock* succ = TInst->getSuccessor(i);// get BB pointer
										// get successor's LIVEOUT/VARKILL/UEVAR
										set<llvm::StringRef> LIVEOUT = LO.find(succ)->second;
										set<llvm::StringRef> VarKill = VK.find(succ)->second;
										set<llvm::StringRef> UEVar = UE.find(succ)->second;
										set<llvm::StringRef> subtrSet (LIVEOUT);
										for (set<llvm::StringRef>::iterator setIt = VarKill.begin(); setIt != VarKill.end(); setIt++) {
												subtrSet.erase(*setIt);
										}
										std::set_union(UEVar.begin(), UEVar.end(), subtrSet.begin(),
														subtrSet.end(), std::inserter(resultSet, resultSet.begin()));
								}
								LO.erase(it);// update the LIVEOUT for this BB
								LO.insert(std::pair<BasicBlock*, std::set<llvm::StringRef>>(tmp,resultSet));
								if (resultSet != originLIVEOUT) {// if changed, add predecessor to worklist
										for (auto predIt = pred_begin(tmp), predEnd = pred_end(tmp); 
														predIt != predEnd; predIt++) {
												BasicBlock* pred = *predIt;
												workList.push_back(pred);
										}
								}
						}

				}

				auto printResult(Function &F, map<BasicBlock*, set<llvm::StringRef>> UE,map<BasicBlock*, set<llvm::StringRef>> VK, 
								map<BasicBlock*, set<llvm::StringRef>> LO){


						//vincent create file for output
						ofstream pathOut = createOutput(F);
						if (!pathOut.is_open()) 
								return 0;

						for (auto& BB : F){
								BasicBlock* key_BB = &BB;
								set<StringRef> VarKill = VK.find(key_BB)->second;
								set<StringRef> UEVar = UE.find(key_BB)->second;
								set<StringRef> LIVEOUT = LO.find(key_BB)->second;
								errs() << "----- "<< key_BB->getName() << " -----\n";
								errs() << "UEVAR: ";

								string bb_name = key_BB->getName();
								pathOut<< "----- "<< bb_name << " -----\n";
								pathOut<<"UEVAR: ";
								string uevar;
								for (set<StringRef>::iterator it = UEVar.begin(); it != UEVar.end(); it++) {
										errs() << *it << " ";
										uevar = *it;
										pathOut<<uevar<<" ";
								}
								pathOut<<"\n";

								errs() << "\n";
								errs() << "VARKILL: ";
								pathOut<<"VARKILL: ";
								string varkill;

								for (set<StringRef>::iterator it = VarKill.begin(); it != VarKill.end(); it++) {
										errs() << *it << " ";
										varkill = *it;
										pathOut<<varkill<<" ";
								}
								pathOut<<"\n";

								errs() << "\n";
								errs() << "LIVEOUT: ";

								pathOut<<"LIVEOUT: ";
								string liveout;
								for (set<StringRef>::iterator it = LIVEOUT.begin(); it != LIVEOUT.end(); it++) {
										errs() << *it << " ";
										liveout = *it;
										pathOut<<liveout<<" ";
								}
								pathOut<<"\n";
								errs()<<"\n";
						}
						pathOut.close();
						return 0;

				}

				bool runOnFunction(Function &F) override {


						if (F.getName() != func_name) return false;

						for (BasicBlock &BB : F) {
								//vincent  init  UEVar/VarKill
								set<StringRef> UEVar;
								UE.insert(std::pair<BasicBlock*, std::set<llvm::StringRef>>(&BB,UEVar));
								set<StringRef> VarKill;
								VK.insert(std::pair<BasicBlock*, std::set<llvm::StringRef>>(&BB,VarKill));

								computeUEandVarKill(F, UEVar, VarKill, BB);

						}
						//vincent compute liveness
						computeLiveOut(F, UE, VK);
						//vincent print UEVar, VarKill, LIVEOUT
						printResult(F, UE, VK, LO);

						return false;
				}
		};
}

char Liveness::ID = 0;
static RegisterPass<Liveness> X("Liveness", "Liveness Analysis");

