#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/PassManager.h"

#include "llvm/Support/raw_ostream.h"
#include <unordered_map>
using namespace std;

using namespace llvm;

namespace {
unordered_map<string, std::vector<string>> Func_Def;
unordered_map<string, std::vector<string>> Func_In;
unordered_map<string, std::vector<string>> Func_Kill;

// This method implements what the pass does
void visitor(Function &F){

    // Here goes what you want to do with a pass
        /* 
        string func_name = "main";
        errs() << "ValueNumbering: " << F.getName() << "\n";
      */  
        // Comment this line
        //if (F.getName() != func_name) return;
        
        // set maps to store every sets 
        unordered_map<string, std::vector<string>> block_UEVar;
        unordered_map<string, std::vector<string>> block_VarKill;
        unordered_map<string, std::vector<string>> block_LiveOut;
        set<string> NotGlobal_Var;

        // retrieve UEVar and VarKill set for each block 
        for (auto& basic_block : F)
        {
            //get block name
            string block_name = string(basic_block.getName());
            // initialize vector to store VarKill and UEVar in this block 
            std::vector<string> VarKill;
            std::vector<string> UEVar;
           
            // start to retrieve UEVar and VarKill sets 
            for (auto& inst : basic_block)
            {  
            //errs() << inst  << "\n";
            if(inst.getOpcode() == Instruction::Alloca){
                AllocaInst *allocaInst = dyn_cast<AllocaInst>(&inst);
                string var = string(allocaInst->getName());
                NotGlobal_Var.insert(var);
                //errs() << var  << "\n";
            }
                if(inst.getOpcode() == Instruction::Load){
                    string var = string(inst.getOperand(0)->getName());

                    // For load situation if we can't fina a var in VarKill or UEVar  
                    // we push it to the vector of UeVar
                    if(std::find(VarKill.begin(), VarKill.end(), var) == VarKill.end()\
                    && std::find(UEVar.begin(), UEVar.end(), var) == UEVar.end()){
                        UEVar.push_back(var);
                    }
                }
                if(inst.getOpcode() == Instruction::Call){
                    //put the liveout function of call function to Use
                   // errs() << inst  << "\n";
                    string var1;
                    //var1 = string(dyn_cast<User>(inst.getOperand(0))->getOperand(0)->getName());
                    //errs() << "var" << inst.getFunction()<< "\n";
                    const Function* func = static_cast<const CallInst&>(inst).getCalledFunction();
                    //errs() << "function called" << func -> getName()<< "\n";
                    errs() << "-----Function:  " << F.getName() << "--called in block:--  " <<basic_block.getName() <<"\n";
                    errs() << "------ UEvar ----\n"; 
                    auto it = Func_In.find(string(func -> getName()));
                    std::vector<std::string>& found_vector = it->second;
                    for (auto& Ins : found_vector)
                    {
                        errs()<<Ins<<" ";
                        UEVar.push_back(Ins);
                    }
                    errs()<<"\n";
                    errs() << "------ VarKill ----\n"; 
                    it = Func_Kill.find(string(func -> getName()));
                    found_vector = it->second;
                    for (auto& Ins : found_vector)
                    {
                        errs()<<Ins<<" ";
                        VarKill.push_back(Ins);
                    }
                        errs()<<"\n";
                        
                }
                if(inst.getOpcode() == Instruction::Store){
                    //store operation part, caculate for VarKill
                    string var1 = "";
                    string var2 = "";
                    // if first operand is a constant, ignore it useless
                    if(isa<ConstantInt>(inst.getOperand(0))){
                        var1 = "";
                    }
                    else{
                        //if first operand is a binary op 
                        var1 = string(dyn_cast<User>(dyn_cast<User>(inst.getOperand(0))\
                        ->getOperand(0))->getOperand(0)->getName());
                        var2 = string(dyn_cast<User>(dyn_cast<User>(inst.getOperand(0))\
                        ->getOperand(1))->getOperand(0)->getName());
                        // if first operand returns empty so it may a register or load
                        if(string(inst.getOperand(0)->getName()) == ""){
                            var1 = string(dyn_cast<User>(inst.getOperand(0))->getOperand(0)->getName());
                        }
                        // if var1 is a constant
                        if(isa<ConstantInt>(dyn_cast<User>(dyn_cast<User>(inst.getOperand(0))\
                            ->getOperand(0))->getOperand(0))){
                            var1 = "";
                        }

                        // if var2 is a constant 
                        if(isa<ConstantInt>(dyn_cast<User>(dyn_cast<User>(inst.getOperand(0))\
                            ->getOperand(1))->getOperand(0))){
                            var2 = "";
                        }
                    }

                    string var_name = string(inst.getOperand(1)->getName());

                    // if var1 is not in VarKill set or UEVar set push it
                    if(std::find(VarKill.begin(), VarKill.end(), var1) == VarKill.end() \
                    && std::find(UEVar.begin(), UEVar.end(), var1) == UEVar.end()){
                        UEVar.push_back(var1);
                    }

                    /* if var2 is not in VarKill set or  UEVar set */
                    if(std::find(VarKill.begin(), VarKill.end(), var2) == VarKill.end() \
                    && std::find(UEVar.begin(), UEVar.end(), var2) == UEVar.end()){
                        UEVar.push_back(var2);
                    }

                    // if var is not already in VarKill push it
                    if(std::find(VarKill.begin(), VarKill.end(), var_name) == VarKill.end()){
                        VarKill.push_back(var_name);
                    }
                }
   
            } //end for inst

            // Save sets to related block
            block_UEVar.insert(make_pair(block_name, UEVar));
            block_VarKill.insert(make_pair(block_name, VarKill));

        } // end for block

        // initialize set for LiveOut
        for (auto& basic_block : F){
            vector<string> emptySet = {};
            block_LiveOut.insert(make_pair(string(basic_block.getName()), emptySet));
        }

        // Compute liveout var by 
        unordered_map<string ,std::vector<string>>::const_iterator block_find;
        bool cont = true;
	set<string> VarKill_Func;
        while(cont){
            //set<string> VarKill_Func;
            cont = false;
	    int w = 0;
            for (auto& basic_block : F){
                w++; 
                std::vector<string> liveOut;
                std::vector<string> liveOut_temp;
                std::vector<string> liveOut_succ;
                std::vector<string> VarKill_succ;
                std::vector<string> VarKill_Out;
                std::vector<string> UEVar_succ;
                std::vector<string> union_succ;
                //errs()<<" for Block:    "<<basic_block.getName()<<"\n";
                unordered_map<string, int> VarKillAnd;
                auto insertOrIncrement = [&VarKillAnd](const std::string& key) {
                    if (VarKillAnd.find(key) == VarKillAnd.end()) {
                                VarKillAnd[key] = 1;
                                    } else {
                                                VarKillAnd[key]++;
                                                }
                    };
                int a = 0;
                for(BasicBlock *succ : successors(&basic_block)){
                    std::vector<string> diff_temp;
                    std::vector<string> union_temp;
                    std::vector<string> and_temp;
                    a++;
                    //errs()<<" Succ Block:    "<<succ->getName()<<"\n";
                    // check if the Liveout can be find of current block
                    block_find = block_LiveOut.find(string(succ->getName()));
                    liveOut_succ = block_find->second;
                    block_find = block_VarKill.find(string(succ->getName()));
                    VarKill_succ = block_find->second;
                    block_find = block_UEVar.find(string(succ->getName()));
                    UEVar_succ = block_find->second;
                    //errs()<<"killl"<<"\n";
                    for(auto it: VarKill_succ){
                        insertOrIncrement(it);
                        //errs()<<it<<" ";
                    }
                    // compute LiveOut(X) - VarKill(X) 
                    std::set_difference(liveOut_succ.begin(), liveOut_succ.end(),\
                    VarKill_succ.begin(), VarKill_succ.end(), std::back_inserter(diff_temp));
                   
                    // add UEVar(X) to liveout
                    std::set_union(diff_temp.begin(), diff_temp.end(),\
                    UEVar_succ.begin(), UEVar_succ.end(), std::back_inserter(union_temp));


                    for(auto it: union_temp){
                        union_succ.push_back(it);
                    }
                    
                }
                for (const auto& pair : VarKillAnd){
                    //errs()<<pair.second<<"  jjjjj  "<<a<<"  ssss  "<<pair.first<<"\n";
                    if(a==pair.second){
                        //errs()<<"must Kill"<<pair.first;
                        VarKill_Func.insert(pair.first);

                    }
                }
		if(w==1){
			block_find = block_VarKill.find(string(basic_block.getName()));
			 VarKill_succ = block_find->second;
			 for (const auto& pair : VarKill_succ){
				//errs()<<pair.second<<"  jjjjj  "<<a<<"  ssss  "<<pair
				//errs()<<"must Kill"<<pair.first;
				 VarKill_Func.insert(pair);
		
			 }
		
		}


                // Compute Union of Successors 
                std::sort(union_succ.begin(), union_succ.end());
                union_succ.erase(std::unique(union_succ.begin(),\
                           union_succ.end()), union_succ.end());

                // retrieve current LiveOut 
                block_find = block_LiveOut.find(string(basic_block.getName()));
                liveOut = block_find->second;

                // If LiveOut(N) is changed mark it 
                if(liveOut != union_succ){
                    cont = true;
                }

                // Update LiveOut 
                auto it = block_LiveOut.find(string(basic_block.getName()));
                it->second = union_succ;
                
                
            }
            for (const auto& elem : NotGlobal_Var) {
                VarKill_Func.erase(elem);
            }
            //errs() << "------ " << F.getName() << " killed ------\n";
	    std::vector<string> Kill_tmp;
            for (const auto& elem : VarKill_Func) {
                Kill_tmp.push_back(elem);
               // errs()<< elem<<"   ";
            }
            Func_Kill.insert(make_pair(string(F.getName()), Kill_tmp));
        }

        // Print out result we already has
        for (auto& basic_block : F){
            std::vector<string> UEVar_temp;
            std::vector<string> VarKill_temp;
            std::vector<string> LiveOut_temp;
            unordered_map<string ,std::vector<string>>::const_iterator block_find;

            block_find = block_UEVar.find(string(basic_block.getName()));
            UEVar_temp = block_find->second;
            std::sort(UEVar_temp.begin(), UEVar_temp.end());
            
            errs() << "------ " << basic_block.getName() << " ------\n";
            errs() << "UEVAR: ";
            for(auto a: UEVar_temp){
                errs() << a << " ";
            }
            errs() << "\n";
                
            block_find = block_VarKill.find(string(basic_block.getName()));
            VarKill_temp = block_find->second;
            std::sort(VarKill_temp.begin(), VarKill_temp.end());
    
            errs() << "VARKILL: ";
            for(auto a: VarKill_temp){
                errs() << a << " ";
            }
            errs() << "\n";

            block_find = block_LiveOut.find(string(basic_block.getName()));
            LiveOut_temp = block_find->second;
            std::sort(LiveOut_temp.begin(), LiveOut_temp.end());
            errs() << "LIVEOUT: ";
            for(auto a: LiveOut_temp){
                errs() << a << " ";
            }
            errs() << "\n"; 

            std::set<std::string> unionSet;
        
            if(basic_block.getName() == "entry"){
                // if it is entry set caculated the in set based on liveout result
                for (auto& ueVar : UEVar_temp) {
                    if (std::find(VarKill_temp.begin(), VarKill_temp.end(), ueVar) == VarKill_temp.end()) {
                        unionSet.insert(ueVar); 
                        }
                    }

                for (auto& liveOut : LiveOut_temp) {
                    if (std::find(VarKill_temp.begin(), VarKill_temp.end(), liveOut) == VarKill_temp.end()) {
                        unionSet.insert(liveOut); 
                    }
                }
                std::vector<std::string> Fun_INT(unionSet.begin(), unionSet.end());
        /*
                errs() << "Function: " << F.getName() << " called\n add variables that may be used "<<"\n";
                for (auto& element : Fun_INT) {

                            errs() << element << " ";
                }
                errs() << "\n ";
        */
                Func_In.insert(make_pair(string(F.getName()), Fun_INT));
            }
        } 
}


// New PM implementation
struct ValueNumberingPass : public PassInfoMixin<ValueNumberingPass> {

  // The first argument of the run() function defines on what level
  // of granularity your pass will run (e.g. Module, Function).
  // The second argument is the corresponding AnalysisManager
  // (e.g ModuleAnalysisManager, FunctionAnalysisManager)
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
      visitor(F);
    unordered_map<string ,std::vector<string>>::const_iterator it;
    it = Func_In.find(string(F.getName()));
    //errs()<< "Check Function:"<< F.getName()<<"\n";
    /*
    if (it != Func_In.end()) {
        // The key was found, and 'it' points to the key-value pair
        // You can access and modify the associated vector using 'it->second'
        std::vector<string> found = it->second;
        errs() << "LIVE OUT for Function: " << F.getName()<< "\n";
        for (auto& Ins : found)
        {
            errs() << Ins << " ";
        }
        errs() << "\n"; 
    }
    */
    return PreservedAnalyses::all();

    
  }
  
    static bool isRequired() { return true; }
};
}



//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {
    LLVM_PLUGIN_API_VERSION, "ValueNumberingPass", LLVM_VERSION_STRING,
    [](PassBuilder &PB) {
      PB.registerPipelineParsingCallback(
        [](StringRef Name, FunctionPassManager &FPM,
        ArrayRef<PassBuilder::PipelineElement>) {
          if(Name == "value-numbering"){
            FPM.addPass(ValueNumberingPass());
            return true;
          }
          return false;
        });
    }};
}
