#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include <string>
#include <map>
#include <typeinfo>
#include "llvm/IR/CFG.h"
#include <list>
#include <iterator>

#define DEBUG_TYPE "Liveness"

using namespace llvm;
using namespace std;

namespace {
struct LivenessAnalysis : public FunctionPass {
  string func_name = "test";
  static char ID;
  LivenessAnalysis() : FunctionPass(ID) {
     //UEVar = new map<BasicBlock*, vector<string>*>;
  }
    map<string, string> var_map;
    map<BasicBlock*, vector<string>*> varKill;
    map<BasicBlock*, vector<string>*> UEVar;
    map<BasicBlock*, vector<string>*> liveOut;
    list<BasicBlock*> blocklist;

    template<typename K, typename V>
    void print_map(map<K, V> const &m)
    {
    	for (auto const &pair: m) {
        	errs()  << "{" << pair.first << ": " << pair.second << "}\n";
    	}	
    }

    // Parse the block from top to down, Add operands not existed in the KillSet and Add destination to the kill set
    void findUEVar(BasicBlock* bb){
        pair<BasicBlock*,vector<string>*> *temp = new pair<BasicBlock*,vector<string>*>;
        auto varKill = new vector<string>;
        auto tempLiveB = new vector<string>;
        auto UEVar = new vector<string>;
        vector<string>::iterator varKillIt;
        vector<string>::iterator UEVarIt;
        errs() << bb->getName() << ":\n";
        
        for (auto& inst : *bb)
        {
            //errs() << "\t"  << inst << "\n";
            errs() << "inst:\t"  << inst<< "\n";
            if(inst.getOpcode() == Instruction::Load){
                errs() << "This is Load"<<"\n";
                string temp;
                llvm::raw_string_ostream op(temp);
                op << inst;
                temp=op.str();
                errs() << "\tload_temp" <<  temp << "\n";
                string load_op=temp.substr(temp.find("="));
                string temp2=temp.substr(0,temp.find("="));
                errs() << "This is load processing before = :"<<load_op<<"\n";
                if(load_op.find("%") != string::npos) {
                    load_op=load_op.substr(load_op.find("%"));
                }
                else {
                    load_op=load_op.substr(0,load_op.find(","));
                }
                load_op=load_op.substr(0,load_op.find(","));
                errs() << "This is load processing after = :"<<load_op<<"\n";
                load_op.erase(remove(load_op.begin(), load_op.end(), ' '), load_op.end());
                temp2.erase(remove(temp2.begin(), temp2.end(), ' '), temp2.end());
                var_map.insert(pair<string,string>(temp2,load_op));
                print_map(var_map);
          }
          if(inst.getOpcode() == Instruction::Store){
            errs() << "This is Store"<<"\n";
          }
          if ((inst.isBinaryOp() /**|| inst.getOpcode()==Instruction::PHI**/) && inst.getOpcode()!=Instruction::ICmp)
          {
            string *op1 = new string;
            string *op2 = new string;
            //string *op3 = new string;
            errs() << "This is Binary"<<"\n";
            auto* ptr = dyn_cast<User>(&inst);
            auto* op3 = dyn_cast<Value>(&inst);
            errs() << "\tptr:\t" << *ptr << "\n";
            int count = 1;
            string temp;
            raw_string_ostream op(temp);
            op << inst;
            temp=op.str();
            for (auto it = ptr->op_begin(); it != ptr->op_end(); ++it) {
                print_map(var_map);
                if (count==1){
                    string temp1;
                    temp1=temp.substr(temp.find("="));
                    temp1=temp1.substr(temp1.find("%"));
                    temp1=temp1.substr(0,temp1.find(","));
                    if(temp1.find("%")==string::npos) {
                        continue;
                    }
                    temp1.erase(remove(temp1.begin(), temp1.end(), ' '), temp1.end());
                    *op1=temp1;
                    auto search = var_map.find(*op1);
                    if (search != var_map.end()){
                        errs() << "\tOp1 is:" << *op1 << "\n";
                        *op1 = search->second;
                    }
                    errs() << "\tOp1 is:" << *op1 << "\nFull is: "<<temp1;
                    if(find(varKill->begin(), varKill->end(), *op1) == varKill->end()) {
                        errs() << "UEVar:\t" << *(*it) << "\n";
                        UEVarIt = UEVar->begin();
                        if (find(UEVar->begin(),UEVar->end(),*op1)==UEVar->end()){
                            UEVar->insert(UEVarIt, *op1);
                        }
                    }   

                }
                else if (count==2){
                    string temp2;
                    //string temp1=*op1;
                    temp2=temp.substr(temp.find(",")+1);
                    temp2.erase(remove(temp2.begin(), temp2.end(), ' '), temp2.end());
                    *op2=temp2;
                    errs() << "\tOp2 is:" << *op2 << "\n";
                    if(temp2.find("%")==string::npos) {
                        break;
                    }
                    auto search = var_map.find(*op2);
                    if (search != var_map.end()){
                        errs() << "\tOp2 is:" << *op2 << "\n";
                        *op2 = search->second;
                    }
                
                    if(find(varKill->begin(), varKill->end(), *op2) == varKill->end()) {
                        errs() << "UEVar:\t" << *(*it) << "\n";
                         UEVarIt = UEVar->begin();
                        if (find(UEVar->begin(),UEVar->end(),*op2)==UEVar->end()){
                            UEVar->insert(UEVarIt, *op2);
                        }
                    } 
                }
                count++;
            }
            string *op3_str = new string;
            *op3_str = temp.substr(0,temp.find("=")); //op3->getName();
            errs() << "op3:\t" << *op3_str << "\n";
            varKillIt = varKill->begin();
            varKill->insert(varKillIt, *op3_str);
          }
        }

        temp->first = bb;
        temp->second = varKill;
        this->varKill.insert(*temp);
        temp->first = bb;
        temp->second = UEVar;
        this->UEVar.insert(*temp);
    }


    bool findLiveOut(BasicBlock* basic_block) {

        vector<string> *liveB;
        auto search = liveOut.find(basic_block);
        if ( search != liveOut.end()){
            liveB = search->second;
        }
        else {
            liveB = new vector<string>;
        }
        // Update the Liveout of this block based on its successors
        // Union(successors) like Liveout(successor) - Killset(successor) + findUEVar(successor)
       auto tempLiveB = new vector<string>;
//        errs() << "--------------\n";
        for (BasicBlock *Succ : successors(basic_block)) {
            vector<string> *lSucc;
            vector<string> *kSucc;
            vector<string> *uSucc;
            vector<string> diff;
            map<BasicBlock*, vector<string>*>::iterator searchS;

            searchS = varKill.find(Succ);
            if (searchS != varKill.end()){
                kSucc = searchS->second;
            }
            else {
                errs() << "!!!!! the block " << Succ <<" is not in Killset list !!!!!\n";
                return false;
            }
            searchS = UEVar.find(Succ);
            if (searchS != UEVar.end()){
                uSucc = searchS->second;
            }
            else {
                errs() << "!!!!! the block is "<< Succ << "not in UEVar list !!!!!\n";
                return false;
            }
            searchS = liveOut.find(Succ);
            if (searchS != liveOut.end()){
                lSucc = searchS->second;
                setDiff(lSucc,kSucc,&diff);
            }

           printVarList("kSucc",kSucc);

            auto tmp2 = new vector<string>;

           printVarList("diff",&diff);
           printVarList("uSucc",uSucc);

            setUnion(&diff,uSucc,tmp2);

            auto tmp3 = new vector<string>;

            setUnion(tmp2,tempLiveB,tmp3);

           printVarList("tmp2",tmp2);
           printVarList("tempLiveB",tempLiveB);
           printVarList("tmp3",tmp3);

            tempLiveB = tmp3;

           printVarList("tempLiveB after",tempLiveB);


        }
        bool changed = false;
        if (tempLiveB->size()!=liveB->size() || search==liveOut.end()){
            changed =true;
        }
        else {
            vector<string>::iterator it;
            for (it = liveB->begin();it != liveB->end();it++){

                //getValueName()
                if(find(tempLiveB->begin(),tempLiveB->end(),*it)==tempLiveB->end()){ //maybe using set_symmetric_difference instead
                    changed = true;
                    break;
                }
            }
        }
        if (changed){
            if(search!=liveOut.end()){
                search->second = tempLiveB;
            }
            else{
                auto temp = new pair<BasicBlock*,vector<string>*>;
                temp->first = basic_block;
                temp->second = tempLiveB;
                this->liveOut.insert(*temp);
            }

        }
        return changed;
    }

    void printVarList(string listName, vector<string> *tmp){
        errs() << listName <<":\n";
        for (auto i1=tmp->begin();i1!=tmp->end();i1++){
            errs() << " "<< *i1 << "\n";
        }
    }

    list<BasicBlock*>* PostOrderTraverse(BasicBlock* bb, list<BasicBlock*> *visited, list<BasicBlock*> *order) {
        visited->push_back(bb);
        for (BasicBlock *succ : successors(bb)) { // Parse the left tree and, then the right tree. Technically, it would be recursive call on every successor
            if (find(visited->begin(), visited->end(), succ)==visited->end()){
                visited = PostOrderTraverse(succ,visited,order);
            }
        }
        order->push_back(bb);
        return visited;
    }

    void performLivenessAnalysis(BasicBlock* bb) {
        bool changed = findLiveOut(bb);
        if(changed){
            for (BasicBlock *pred : predecessors(bb)) {
                auto el = find(blocklist.begin(), blocklist.end(), pred);
                if(el==blocklist.end()){
                    blocklist.push_back(pred);
                }
            }
        }
    }

    void printBlockMap(map<BasicBlock*, vector<string>*> *inp){
        errs() << "---------LiveOut-begin----------\n";
        for (map<BasicBlock*, vector<string>*>::iterator block = inp->begin();block != inp->end();block++){
            errs() << block->first->getName() << ":\n\t";
            for(auto var = block->second->begin(); var!=block->second->end();var++){
                errs() << *var << ", ";
            }
            errs() << "\n";
        }
        errs() << "---------LiveOut-end----------\n";
    }

    bool static compareStrings(string str1, string str2){
        errs() << "str1:" << str1 << "\tstr2:" << str2 << "\tcmp:" <<to_string(str1.compare(str2)) << "\n";
        return str1.compare(str2)==0;
    }

    void setDiff(vector<string> *s1,vector<string> *s2,vector<string> *s3){
        for (auto it=s1->begin();it!=s1->end();it++){
            if(find(s2->begin(),s2->end(),*it)==s2->end()){
                s3->insert(s3->end(),*it);
            }
        }
    }

    void setUnion(vector<string> *s1,vector<string> *s2,vector<string> *s3){
        *s3 = *s1;
        for (auto it=s2->begin();it!=s2->end();it++){
            if(find(s1->begin(),s1->end(),*it)==s1->end()){

                s3->insert(s3->end(),*it);
            }
        }
    }

    void printTraverseOrder( list<BasicBlock*> *visitedBlocks,  list<BasicBlock*> *order){
        errs() << "visited:\n";
        for(auto itt = visitedBlocks->begin(); itt!=visitedBlocks->end();itt++){
            errs() << *itt << ", ";
        }
        errs() << "\n";

        errs() << "PO:\n";
        for(auto itt = order->begin(); itt!=order->end();itt++){
            errs() << *itt << ", ";
        }
        errs() << "\n";
    }

  bool runOnFunction(Function &F) override {
        // if (F.getName().compare("main")==0){
        //     return false;
        // }
        // else{
    errs() << "-----------Inside Function: " << F.getName() << "-----------\n";
        // }
    varKill.clear();
    UEVar.clear();
    liveOut.clear();
    blocklist.clear();
    // initialize UEVar and the Killset on all blocks
    for (auto& basic_block : F) {
        findUEVar(&basic_block);
    }
    BasicBlock &basicBlock = F.getEntryBlock();
    list<BasicBlock*> *visited = new list<BasicBlock*>;
    auto visitedBlocks = PostOrderTraverse(&basicBlock,visited,&blocklist);

    printTraverseOrder(visited, &blocklist);

    //blocklist.push_back(&basicBlock); // initialize the blocklist to the entry block, then all others will be automatically added from there
    int i = 0;
    while (!blocklist.empty()) // Call Liveness on the entry block until blocklist is empty
    {
        auto block = blocklist.front();
        performLivenessAnalysis(block);
        printBlockMap(&liveOut);
        blocklist.pop_front();
        i++;
    }
    printBlockMap(&liveOut);
    return false;
  }

}; // end of struct Liveness
}  // end of anonymous namespace

char LivenessAnalysis::ID = 0;
static RegisterPass<LivenessAnalysis> X("LivenessAnalysis", "Liveness Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
