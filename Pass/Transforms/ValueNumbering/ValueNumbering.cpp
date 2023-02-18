#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/PassManager.h"

#include "llvm/Support/raw_ostream.h"
#include <unordered_map>
using namespace std;

using namespace llvm;

namespace {

// This method implements what the pass does
void visitor(Function &F){

    // Here goes what you want to do with a pass
    
		string func_name = "main";
	    errs() << "ValueNumbering: " << F.getName() << "\n";
	    
	    // Comment this line
        //if (F.getName() != func_name) return;
		
        // set maps to store every sets 
        unordered_map<string, std::vector<string>> block_UEVar;
        unordered_map<string, std::vector<string>> block_VarKill;
        unordered_map<string, std::vector<string>> block_LiveOut;

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
                if(inst.getOpcode() == Instruction::Load){
                    string var = string(inst.getOperand(0)->getName());

                    // For load situation if we can't fina a var in VarKill or UEVar  
		    // we push it to the vector of UeVar
                    if(std::find(VarKill.begin(), VarKill.end(), var) == VarKill.end()\
				    && std::find(UEVar.begin(), UEVar.end(), var) == UEVar.end()){
                        UEVar.push_back(var);
                    }
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
        while(cont){
            cont = false;
            for (auto& basic_block : F){
                std::vector<string> liveOut;
                std::vector<string> liveOut_temp;
                std::vector<string> liveOut_succ;
                std::vector<string> VarKill_succ;
                std::vector<string> UEVar_succ;
                std::vector<string> union_succ;
          
                for(BasicBlock *succ : successors(&basic_block)){
                    std::vector<string> diff_temp;
                    std::vector<string> union_temp;

                    // check if the Liveout can be find of current block
                    block_find = block_LiveOut.find(string(succ->getName()));
                    liveOut_succ = block_find->second;
                    block_find = block_VarKill.find(string(succ->getName()));
                    VarKill_succ = block_find->second;
                    block_find = block_UEVar.find(string(succ->getName()));
                    UEVar_succ = block_find->second;

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
