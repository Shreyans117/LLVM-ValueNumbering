#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include <string>
#include <unordered_map>
#include <typeinfo>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "ValueNumbering"

using namespace llvm;

namespace {
struct ValueNumbering : public FunctionPass {
    string func_name = "test";
    static char ID;
    ValueNumbering() : FunctionPass(ID) {}
	
    unordered_map<string, int> hashMap;
    unordered_map<string, string> var_map;
    int value_number = 1;
    
    string getOperand(Use *it){
        if ((*it)->hasName()){
            return (*it)->getName();
        }
        else if (isa<ConstantInt>(it)){
                auto* constantVal = dyn_cast<ConstantInt>(it);
                return constantVal->getValue().toString(10,1);
            }
            else {return ""; }
    }
    
    int populateHashMap(string *operand,bool *found){
    	errs() << "Inside Hash Function:"<<*operand<<"\n";
    	string str=*operand;
    	str.erase(std::remove(str.begin(), str.end(), ' '), str.end());
    	*operand=str;
        auto search = hashMap.find(*operand);
        auto retvalue_number = value_number;
        if (search != hashMap.end()){
            *found = true;
            retvalue_number = search->second;
        }
        else{
            *found = false;
            hashMap.insert(pair<string,int>(*operand,value_number++));
        }
        return retvalue_number;
    }

    bool runOnFunction(Function &F) override {
	string *op1 = new string;
      	int op_1;
      	string *op2 = new string;
      	int op_2;
      	string *op3 = new string;
     	int op_3;
     	string *operand = new string;
      	string *hashKey = new string;
      	string *instructionsBinary = new string;

      	hashMap.clear();   
        errs() << "ValueNumbering: " << F.getName() << "\n";
        if (F.getName() != func_name) return false;

        for (auto& basic_block : F)
        {
            for (auto& inst : basic_block)
            {
                errs() << inst << "\n";
                if(inst.getOpcode() == Instruction::Load){
                    errs() << "This is Load"<<"\n";
                    auto* ptr = dyn_cast<User>(&inst);
                    for (auto it = ptr->op_begin(); it != ptr->op_end(); ++it) {
                        errs() << "\t" <<  *(*it) << "\n";
                    }
                    string temp;
                    llvm::raw_string_ostream op(temp);
                    op << inst;
                    temp=op.str();
                    errs() << "\tload_temp" <<  temp << "\n";
                    string load_op=temp.substr(temp.find("="));
                    if(load_op.find("%") != std::string::npos) {
                    	load_op=load_op.substr(load_op.find("%"));
                    }
                    else {
                   	load_op=load_op.substr(0,load_op.find("="));
                    }
                    load_op=load_op.substr(0,load_op.find(","));
                    errs() << "\tload_op: " <<  load_op << "\n";
                    bool *found = new bool(false);
                    string *load_op1=new string;
                    *load_op1=load_op;
                    int load_op_vn=populateHashMap(load_op1,found);
                    if (*found){
                    	load_op=temp.substr(0,temp.find("="));
                    	*load_op1=load_op;
                    	errs() << "\tDuplicate load value found: " <<  load_op << "\n";
                    	hashMap.insert(pair<string,int>(*load_op1,load_op_vn));
                    }
                    else{
                    	load_op=temp.substr(0,temp.find("="));
                    	*load_op1=load_op;
                    	hashMap.insert(pair<string,int>(*load_op1,value_number++));
                    }
                    errs() << "\tload_op" <<  load_op << "\n";
                }
                if(inst.getOpcode() == Instruction::Store){
                    errs() << "This is Store"<<"\n";
                    
                    auto* ptr = dyn_cast<User>(&inst);
                    for (auto it = ptr->op_begin(); it != ptr->op_end(); ++it) {
                        errs() << "\t" <<  *(*it) << "\n";
                    }
                    string temp;
                    llvm::raw_string_ostream op(temp);
                    op << inst;
                    temp=op.str();
                    errs() << "\tstore_temp" <<  temp << "\n";
                    string store_op=temp.substr(temp.find("="));
                    if(store_op.find("%") != std::string::npos) {
                    	store_op=store_op.substr(store_op.find("%"));
                    }
                    else {
                   	store_op=store_op.substr(0,store_op.find("="));
                    }
                    store_op=store_op.substr(0,store_op.find(","));
                    errs() << "\tstore_op: " <<  store_op << "\n";
                    bool *found = new bool(false);
                    string *store_op1=new string;
                    *store_op1=store_op;
                    int store_op_vn=populateHashMap(store_op1,found);
                    if (*found){
                    	store_op=temp.substr(0,temp.find("="));
                    	*store_op1=store_op;
                    	errs() << "\tDuplicate load value found: " <<  store_op << "\n";
                    	hashMap.insert(pair<string,int>(*store_op1,store_op_vn));
                    }
                    else{
                    	store_op=temp.substr(0,temp.find("="));
                    	*store_op1=store_op;
                    	hashMap.insert(pair<string,int>(*store_op1,value_number++));
                    }
                }
                if (inst.isBinaryOp())
                {
                    errs() << "Op Code:" << inst.getOpcodeName()<<"\n";
                    if(inst.getOpcodeName()=="add" || inst.getOpcode() == Instruction::Add){
                        errs() << "This is Addition"<<"\n";
                        *operand = "+";
                    }
                    if(inst.getOpcodeName()=="sub" || inst.getOpcode() == Instruction::Sub){
                        errs() << "This is Subtraction"<<"\n";
                        *operand = "-";
                    }
                    if(inst.getOpcodeName()=="mul" || inst.getOpcode() == Instruction::Mul){
                        errs() << "This is Multiplication"<<"\n";
                        *operand = "*";
                    }
                    if(inst.getOpcodeName()=="udiv" || inst.getOpcode() == Instruction::UDiv){
                        errs() << "This is Division"<<"\n";
                        *operand = "/";
                    }
                    
                    // see other classes, Instruction::Sub, Instruction::UDiv, Instruction::SDiv
                    // errs() << "Operand(0)" << (*inst.getOperand(0))<<"\n";
                    auto* ptr = dyn_cast<User>(&inst);
                    auto* val = dyn_cast<Value>(&inst);
                    *op3 = val->getName();
                    string temp;
                    llvm::raw_string_ostream op(temp);
                    op << inst;
                    temp=op.str();
                    *op3=temp.substr(0,temp.find("="));
                    //*operand="add";//temp.substr(temp.find("=")+1,temp.find("=")+5);
                    if (temp.find("add") != std::string::npos) {
			*operand="add";
		     }
		     else if (temp.find("sub") != std::string::npos) {
			*operand="sub";
		     }
		     else if (temp.find("mul") != std::string::npos) {
			*operand="mul";
		     }
		     else if (temp.find("div") != std::string::npos) {
			*operand="div";
		     }
                    errs() << "\tOp3 is:" << *op3 << "\nFull is: "<<temp;
		     int i = 1;
		    //errs() << "\t" << *ptr << "\n";
                    for (auto it = ptr->op_begin(); it != ptr->op_end(); ++it) {
                        errs() << "\t" <<  *(*it) << "\n";
                        if (i==1){
                            *op1=getOperand(it);
                            errs() << "\tOp1 is:" << *op1 << "\n";
                            string temp1;
                            temp1=temp.substr(temp.find("="));
                            temp1=temp1.substr(temp1.find("%"));
                            temp1=temp1.substr(0,temp1.find(","));
                            *op1=temp1;
                            errs() << "\tOp1 is:" << *op1 << "\nFull is: "<<temp1;

                        }
                        else if (i==2){
                            *op2=getOperand(it);
                            errs() << "\tOp2 is:" << *op2 << "\n";
                            string temp2;
                            //string temp1=*op1;
                            temp2=temp.substr(temp.find(",")+1);
                            *op2=temp2;
                            errs() << "\tOp2 is:" << *op2 << "\n";
                        }
                        i++;
                        // if ((*it)->hasName()) 
			    // errs() << (*it)->getName() << "\n";                      
                    }
                    bool *found = new bool(false);
                    op_1 = populateHashMap(op1,found);
                    op_2 = populateHashMap(op2,found);
                    *hashKey = "%"+to_string(op_1) + *operand + "%"+to_string(op_2);
                    string instruction = *op3 + " = " + *op1 + *operand + *op2;
                   *instructionsBinary = *instructionsBinary + instruction + "\n";
                    op_3 = populateHashMap(hashKey,found);
                    if (*found){
                         errs() << "---------------- Duplicates found: " << *op1 << *operand << *op2 << " ----------------\n" << op_1 << "<<<" << op_2 << "<<<" << op_3 <<"<<<\n";
                        *found = false;
                    }
                    hashMap.insert(pair<string,int>(*op3,op_3));
                } // end if
            } // end for inst
            errs() << "instructions: \n" << *instructionsBinary;
        } // end for block
        return false;
    } // end runOnFunction
}; // end of struct ValueNumbering
}  // end of anonymous namespace

char ValueNumbering::ID = 0;
static RegisterPass<ValueNumbering> X("ValueNumbering", "ValueNumbering Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
