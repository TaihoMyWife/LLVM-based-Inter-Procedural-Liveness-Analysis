#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include <unordered_map>
#include <typeinfo>
using namespace std;

using namespace llvm;
using PointerPair = std::pair<std::string, std::string>;
using ParameterPair = std::pair<std::string, int>;

namespace {
struct CallGraphPass : public PassInfoMixin<CallGraphPass> {
    unordered_map<string, std::vector<string>> Func_KillB;
    unordered_map<string, std::vector<string>> Func_In;
    unordered_map<string, std::vector<string>> Func_Kill;
    unordered_map<string, std::set<string>> Func_NoGlobal;

    unordered_map<string, std::vector<string>> Pointer_Use;
    unordered_map<string, std::vector<string>> Pointer_Kill;
    unordered_map<string, std::vector<PointerPair>> Pointer_Pair;
    unordered_map<string, std::vector<ParameterPair>> Func_Para;

    unordered_map<string, std::vector<string>> Pointers;

    unordered_map<string, std::set<PointerPair>> May_Alias;
    unordered_map<string, std::set<PointerPair>> No_Alias;
    unordered_map<string, std::set<PointerPair>> Partial_Alias;
    unordered_map<string, std::set<PointerPair>> Must_Alias;

    unordered_map<string, std::vector<string>> Func_KillB_Pre;
    unordered_map<string, std::vector<string>> Func_In_Pre;
    unordered_map<string, std::vector<string>> Func_Kill_Pre;

    std::string valueToString(const llvm::Value *V) {
        std::string ValueStr;
        llvm::raw_string_ostream RSO(ValueStr);
        V->print(RSO);
        return RSO.str(); // Returns the string representation of the Value
    }

    // Function to print elements of a vector that do not contain '_pointer'
    void printVectorWithoutPointer(const std::vector<std::string>& vec, const std::string& label) {
        llvm::errs() << label << ": ";
        for (const auto& element : vec) {
            if (element.find("_pointer") == std::string::npos) { // Check if '_pointer' is not in the string
                llvm::errs() << element << " ";
            }
        }
        llvm::errs() << "\n";
    }

    void printVectorWithPointer(const std::vector<std::string>& vec, const std::string& label) {
        llvm::errs() << label << ": ";
        for (const auto& element : vec) {
            if (element.find("_pointer") != std::string::npos) { // Check if '_pointer' is in the string
                std::string modifiedElement = element;
                size_t pos = modifiedElement.find("_pointer");
                if (pos != std::string::npos) {
                    modifiedElement.erase(pos, strlen("_pointer")); // Remove "_pointer" from the string
                }
                llvm::errs() << modifiedElement << " ";
            }
        }
        llvm::errs() << "\n";
    }

    void printFuncMapWithoutPointer(const std::unordered_map<std::string, std::vector<std::string>>& funcMap, const std::string& label) {
        for (const auto& pair : funcMap) {
            const std::string& functionName = pair.first;
            const std::vector<std::string>& elementList = pair.second;

            llvm::errs() << "Function: " << functionName << " " << label << ": ";
            for (const std::string& element : elementList) {
                if (element.find("_pointer") == std::string::npos) { // Check if '_pointer' is not in the string
                    llvm::errs() << element << " ";
                }
            }
            llvm::errs() << "\n";
        }
    }

    void printFuncMapWithPointer(const std::unordered_map<std::string, std::vector<std::string>>& funcMap, const std::string& label) {
        for (const auto& pair : funcMap) {
            const std::string& functionName = pair.first;
            const std::vector<std::string>& elementList = pair.second;

            llvm::errs() << "Function: " << functionName << " " << label << ": ";
            for (const std::string& element : elementList) {
                if (element.find("_pointer") != std::string::npos) { // Check if '_pointer' is in the string
                    std::string modifiedElement = element;
                    size_t pos = modifiedElement.find("_pointer");
                    if (pos != std::string::npos) {
                        modifiedElement.erase(pos, strlen("_pointer")); // Remove "_pointer" from the string
                    }
                    llvm::errs() << modifiedElement << " ";
                }
            }
            llvm::errs() << "\n";
        }
    }

    // Find the var which pointer points to  and add it to UseVar
    void handlePointer(const std::string& pointerIns, 
                    const std::string& functionName,
                    const unordered_map<string, std::vector<PointerPair>>& Pointer_Pair,
                    const unordered_map<string, std::set<string>>& Func_NoGlobal,
                    std::vector<std::string>& UEVar) {
        // Remove "_pointer" from the instruction name for the lookup
        std::string pointerBase = pointerIns.substr(0, pointerIns.find("_pointer"));

        auto funcIt = Pointer_Pair.find(functionName);
        if (funcIt != Pointer_Pair.end()) {
            for (const auto& pair : funcIt->second) {
                if (pair.first == pointerBase) {
                    std::string pointedVar = pair.second;  // Get the variable name it points to
                    // Check if the variable is not a non-global variable for the current function
                    auto ngIt = Func_NoGlobal.find(functionName);
                    if (ngIt == Func_NoGlobal.end() || ngIt->second.find(pointedVar) == ngIt->second.end()) {
                        UEVar.push_back(pointedVar);       // Add the variable name to UEVar
                        llvm::errs() << "In function " << functionName << ", pointer " << pointerIns << " points to: " << pointedVar << "\n";
                    } else {
                        llvm::errs() << "Variable " << pointedVar << " is a non-global variable in function " << functionName << " and won't be added\n";
                    }
                    return; // Stop once the match is found
                }
            }
            //llvm::errs() << "No matching pointer pair found for: " << pointerBase << " in function " << functionName << "\n";
        } else {
            //llvm::errs() << "No pointer pair information for function: " << functionName << "\n";
        }
    }

    void handlePointerForVarKill(const std::string& pointerIns, 
                                const std::string& functionName,
                                const unordered_map<string, std::vector<PointerPair>>& Pointer_Pair,
                                const unordered_map<string, std::set<string>>& Func_NoGlobal,
                                std::vector<std::string>& VarKill) {
        std::string pointerBase = pointerIns.substr(0, pointerIns.find("_pointer"));

        auto funcIt = Pointer_Pair.find(functionName);
        if (funcIt != Pointer_Pair.end()) {
            std::vector<std::string> potentialPointedVars;
            for (const auto& pair : funcIt->second) {
                if (pair.first == pointerBase) {
                    std::string pointedVar = pair.second;
                    auto ngIt = Func_NoGlobal.find(functionName);
                    if (ngIt == Func_NoGlobal.end() || ngIt->second.find(pointedVar) == ngIt->second.end()) {
                        potentialPointedVars.push_back(pointedVar);
                    }
                }
            }
            if (potentialPointedVars.size() == 1) {
                VarKill.push_back(potentialPointedVars.front());
                llvm::errs() << "Variable " << potentialPointedVars.front() << " added to VarKill for function " << functionName << "\n";
            } else {
                llvm::errs() << "Multiple or no pointed variables found for " << pointerBase << " in function " << functionName << ", none added to VarKill\n";
            }
        } else {
            llvm::errs() << "No pointer pair information for function: " << functionName << "\n";
        }
    }

// Main code block remains the same

    void visitor(Function &F){

        unordered_map<string, std::vector<string>> block_UEVar;
        unordered_map<string, std::vector<string>> block_VarKill;
        unordered_map<string, std::vector<string>> block_LiveOut;
        set<string> NotGlobal_Var;

        // retrieve UEVar and VarKill set for each block 
        for (auto& basic_block : F)
        {
            string block_name = string(basic_block.getName());
            // initialize vector to store VarKill and UEVar in this block 
            std::vector<string> VarKill;
            std::vector<string> UEVar;
            std::vector<string> VarKillP;
            std::vector<string> UEVarP;
            //errs() << "---sss--- " << basic_block.getName() << " ---sss---\n";
            // start to retrieve UEVar and VarKill sets 
            for (auto& inst : basic_block)
            {  
                //errs() << "inst: "<< inst  << "\n";
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
                        //errs() <<"USE0 "<< var  << "\n";
                        UEVar.push_back(var);
                    }
                    LoadInst *loadInst = dyn_cast<LoadInst>(&inst);
                    if (loadInst) {
                        Value *pointerOperand = loadInst->getPointerOperand(); // The pointer being dereferenced

                        if (pointerOperand->getType()->isPointerTy()) {
                            std::string pointerName = pointerOperand->hasName() ? pointerOperand->getName().str() : "<Unnamed Pointer>";

                            //errs() << "Load Instruction: Load from " << pointerName << "\n";
                            Pointer_Use[F.getName().str()].push_back(pointerName);
                            pointerName = pointerName + "_pointer";
                            if(std::find(VarKill.begin(), VarKill.end(), pointerName) == VarKill.end() \
                            && std::find(UEVar.begin(), UEVar.end(), pointerName) == UEVar.end()){
                                //errs() <<"USE3 "<< var2  << "\n";
                                UEVar.push_back(pointerName);
                            }

                        }
                    }
                }
                if(inst.getOpcode() == Instruction::Call){
                    //put the liveout function of call function to Use
                    string var1;
                    const Function* func = static_cast<const CallInst&>(inst).getCalledFunction();
                    //errs() << "function called" << func -> getName()<< "\n";
                    //errs() << "-----Function:  " << F.getName() << "--called in block:--  " <<basic_block.getName() <<"\n";
                                 
                    const CallInst *callInst = dyn_cast<CallInst>(&inst);
                    if (callInst) {
                        const Function *func = callInst->getCalledFunction();
                        if (func) { // Direct function call
                            llvm::errs() << "Function called: " << func->getName() << "\n";
                            auto funcName = func->getName().str();
                            auto it = Func_Para.find(funcName);
                            if (it != Func_Para.end()) {
                                auto &paramPairs = it->second;
                                for (unsigned i = 0; i < callInst->getNumOperands() - 1; ++i) {
                                    Value *arg = callInst->getArgOperand(i);
                                    std::string paramName = "<Param Not Found>";
                                    if (i < paramPairs.size() && paramPairs[i].second == static_cast<int>(i)) {
                                        paramName = paramPairs[i].first;
                                    }
                                    llvm::errs() << "Parameter " << i << " (" << paramName << "): ";
                                    if (arg->getType()->isPointerTy()) {
                                        std::string argName = arg->hasName() ? arg->getName().str() : "<Unnamed Pointer Arg>";
                                        llvm::errs() << "Pointer Argument: " << argName << "\n";
                                        PointerPair pointers = {paramName, argName};
                                        Pointer_Pair[F.getName().str()].push_back(pointers);
                                    }
                                    else {
                                        llvm::errs() << "Non-pointer Argument\n";
                                    }
                                }
                            } else {
                                llvm::errs() << "No parameter information found for function " << funcName << "\n";
                            }
                        } else {
                            llvm::errs() << "Indirect call.\n";
                        }
                    }
                    
                    auto it = Func_In.find(string(func->getName()));
                    if (it != Func_In.end()) {
                        std::vector<std::string>& found_vector = it->second;
                        for (auto& Ins : found_vector) {
                            if (Ins.find("_pointer") != std::string::npos) {
                                // Handle special pointer case
                                handlePointer(Ins, string(func->getName()), Pointer_Pair, Func_NoGlobal, UEVar);

                                // Define a lambda function for checking in May_Alias
                                auto checkMayAlias = [&](const std::string& funcName) {
                                    auto mayAliasIt = May_Alias.find(funcName);
                                    if (mayAliasIt != May_Alias.end()) {
                                        const auto& pointerPairs = mayAliasIt->second;
                                        for (const auto& pointerPair : pointerPairs) {
                                            if (pointerPair.first == Ins || pointerPair.second == Ins) {
                                                // Found the same pointer in May_Alias for this function
                                                errs() << "Found matching pointer in May_Alias for function " << funcName << ": " << Ins << "\n";
                                            }
                                        }
                                    }
                                };

                                // Check in May_Alias for the same pointer for this specific function using both representations
                                std::string functionNameStr = F.getName().str(); // std::string version
                                std::string functionNameStrMethod = func->getName().str(); // method version

                                checkMayAlias(functionNameStr);
                                if (functionNameStr != functionNameStrMethod) {
                                    checkMayAlias(functionNameStrMethod);
                                }
                            } else {
                                // Regular case
                                UEVar.push_back(Ins);
                            }
                        }
                    } else {
                        // Not found, so UEVar remains empty
                        errs() << "UEVar is null for function " << func->getName().str() << "\n";
                    }
                    auto it1 = Func_Kill.find(string(func->getName()));
                    if (it1 != Func_In.end()) {
                        std::vector<std::string>& found_vector1 = it1->second;
                        for (auto& Ins : found_vector1) {
                            if (Ins.find("_pointer") != std::string::npos) {
                                // Handle special pointer case
                                handlePointer(Ins, string(func->getName()), Pointer_Pair, Func_NoGlobal, UEVar);

                                // Define a lambda function for checking in May_Alias
                                auto checkMayAlias = [&](const std::string& funcName) {
                                    auto mayAliasIt = Must_Alias.find(funcName);
                                    if (mayAliasIt != Must_Alias.end()) {
                                        const auto& pointerPairs = mayAliasIt->second;
                                        for (const auto& pointerPair : pointerPairs) {
                                            if (pointerPair.first == Ins || pointerPair.second == Ins) {
                                                // Found the same pointer in May_Alias for this function
                                                errs() << "Found matching pointer in Must_Alias for function " << funcName << ": " << Ins << "\n";
                                            }
                                        }
                                    }
                                };

                                // Check in May_Alias for the same pointer for this specific function using both representations
                                std::string functionNameStr = F.getName().str(); // std::string version
                                std::string functionNameStrMethod = func->getName().str(); // method version

                                checkMayAlias(functionNameStr);
                                if (functionNameStr != functionNameStrMethod) {
                                    checkMayAlias(functionNameStrMethod);
                                }
                            } else {
                                // Regular case
                                UEVar.push_back(Ins);
                            }
                        }
                    } else {
                        // Not found, so UEVar remains empty
                        errs() << "VarKill is null for function " << func->getName().str() << "\n";
                    }
                    //errs() << "------ VarKill ----"<< string(func -> getName()) <<"\n"; 

                                            
                }
                if(inst.getOpcode() == Instruction::Store){
                    //store operation part, caculate for VarKill
                    string var1 = "";
                    string var2 = "";

                    //errs() << "Store 0\n";
                    // if first operand is a constant, ignore it useless
                    if(isa<ConstantInt>(inst.getOperand(0))){
                        var1 = "";
                    }
                    else{
                        //if first operand is a binary op 
                        //errs() << "Store 1\n";
                        //var1 = string(dyn_cast<User>(dyn_cast<User>(inst.getOperand(0))->getOperand(0))->getOperand(0)->getName());

                        
                        if (auto *UserOp1 = dyn_cast<User>(inst.getOperand(0))) {
                            if (auto *UserOp2 = dyn_cast<User>(UserOp1->getOperand(0))) {
                                if (UserOp2->getOperand(0)->hasName()) {
                                    var1 = UserOp2->getOperand(0)->getName().str();
                                }
                            }
                            if (UserOp1->getNumOperands() > 1) { // Check if the second operand exists
                                if (auto *UserOp3 = dyn_cast<User>(UserOp1->getOperand(1))) {
                                    if (UserOp3->getOperand(0)->hasName()) {
                                        var2 = UserOp3->getOperand(0)->getName().str();
                                    }
                                }
                            }
                        }

                        //var2 = string(dyn_cast<User>(dyn_cast<User>(inst.getOperand(0))->getOperand(1))->getOperand(0)->getName());
                        // if first operand returns empty so it may a register or load
                        if (!inst.getOperand(0)->hasName()) {
                            if (auto *UserOp1 = dyn_cast<User>(inst.getOperand(0))) {
                                if (UserOp1->getOperand(0)->hasName()) {
                                    var1 = UserOp1->getOperand(0)->getName().str();
                                }
                            }
                        }
                        /*
                        if(string(inst.getOperand(0)->getName()) == ""){
                            var1 = string(dyn_cast<User>(inst.getOperand(0))->getOperand(0)->getName());
                        }
                        if(isa<ConstantInt>(dyn_cast<User>(dyn_cast<User>(inst.getOperand(0))\
                            ->getOperand(0))->getOperand(0))){
                            var1 = "";
                        }
                        */
                        // if var2 is a constant 
                        if (auto *outerUser = dyn_cast<User>(inst.getOperand(0))) {
                            if (auto *innerUser = dyn_cast<User>(outerUser->getOperand(1))) {
                                if (auto *operand = innerUser->getOperand(0)) {
                                    if (isa<ConstantInt>(operand)) {
                                        var2 = "";
                                    }
                                }
                            }
                        }
                         //errs() << "Store 4\n";
                    }
                    
                    string var_name = string(inst.getOperand(1)->getName());
                    //errs() <<"var1:"<< var1 << "var2:" << var2 << "var_name:"<< var_name<< "\n";

                    // if var1 is not in VarKill set or UEVar set push it
                    if(std::find(VarKill.begin(), VarKill.end(), var1) == VarKill.end() \
                    && std::find(UEVar.begin(), UEVar.end(), var1) == UEVar.end()){
                        //errs() <<"USE2 "<< var1  << "\n";
                        UEVar.push_back(var1);
                    }

                    /* if var2 is not in VarKill set or  UEVar set */
                    if(std::find(VarKill.begin(), VarKill.end(), var2) == VarKill.end() \
                    && std::find(UEVar.begin(), UEVar.end(), var2) == UEVar.end()){
                        //errs() <<"USE3 "<< var2  << "\n";
                        UEVar.push_back(var2);
                    }
                    //errs() <<"What happen"<< "\n";
                    // if var is not already in VarKill push it
                    if(std::find(VarKill.begin(), VarKill.end(), var_name) == VarKill.end()){
                        //errs() <<"KILL1 "<< var_name  << "\n";
                        VarKill.push_back(var_name);
                    }

                    StoreInst *storeInst = dyn_cast<StoreInst>(&inst);
                    if (storeInst) {
                        Value *storedValue = storeInst->getValueOperand(); // This is 'b' in '*a = b'
                        Value *pointerOperand = storeInst->getPointerOperand(); // This is 'a' in '*a = b'

                        if (pointerOperand->getType()->isPointerTy()) {
                            //std::string pointerName = pointerOperand->hasName() ? pointerOperand->getName().str() : "<Unnamed Pointer>";
                            //std::string valueName = storedValue->hasName() ? storedValue->getName().str() : "<Unnamed Value>";
                            std::string pointerName = storeInst->getPointerOperand()->hasName() ? storeInst->getPointerOperand()->getName().str() : "<Unnamed Pointer>";
                            std::string valueName = storeInst->getValueOperand()->hasName() ? storeInst->getValueOperand()->getName().str() : "<Unnamed Var>";
                            if (pointerName != "<Unnamed Pointer>") {
                                PointerPair pointers = {pointerName, valueName};
                                Pointer_Pair[F.getName().str()].push_back(pointers);
                                //errs() << "Store Instruction: *" << pointerName << " = " << valueName << "\n";

                                // Remove any suffix like '.addr' from the pointer name for comparison
                                size_t suffixPos = pointerName.find(".addr");
                                std::string basePointerName = (suffixPos != std::string::npos) ? pointerName.substr(0, suffixPos) : pointerName;

                                if (basePointerName != valueName) {
                                    pointerName = pointerName + "_pointer";
                                    if (std::find(VarKill.begin(), VarKill.end(), pointerName) == VarKill.end()) {
                                        VarKill.push_back(pointerName);
                                    }
                                }
                            }
                        }
                    }
                }
   
            } //end for inst

            // Save sets to related block
            block_UEVar.insert(make_pair(block_name, UEVar));
            block_VarKill.insert(make_pair(block_name, VarKill));

        } // end for block

        Func_NoGlobal[F.getName().str()]=NotGlobal_Var;
        // initialize set for LiveOut
        for (auto& basic_block : F){
            vector<string> emptySet = {};
            block_LiveOut.insert(make_pair(string(basic_block.getName()), emptySet));
        }

        // Compute liveout var by 
        unordered_map<string ,std::vector<string>>::const_iterator block_find;
        bool cont = true;
	    set<string> VarKill_Func;
        int a =0;
        while(cont&&a<5){
            //set<string> VarKill_Func;
            cont = false;
	        int w = 0;
            a++;
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
                    if(a==pair.second){
                        //errs()<<"must Kill"<<pair.first;
                        VarKill_Func.insert(pair.first);

                    }
                }
                if(w==1){
                    block_find = block_VarKill.find(string(basic_block.getName()));
                    VarKill_succ = block_find->second;
                    for (const auto& pair : VarKill_succ){
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
            //errs() << "------ " << F.getName() << " var must killed ------\n";
	        std::vector<string> Kill_tmp;
            for (const auto& elem : VarKill_Func) {
                Kill_tmp.push_back(elem);
                //errs()<< elem<<"   ";
            }
            Func_Kill[string(F.getName())] =  Kill_tmp;
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
            
            llvm::errs() << "------ " << basic_block.getName() << " ------\n";
            printVectorWithoutPointer(UEVar_temp, "UEVAR");
            printVectorWithoutPointer(VarKill_temp, "VARKILL");
            printVectorWithoutPointer(LiveOut_temp, "LIVEOUT");

            //errs() << basic_block.getName()<< "-----check blocks\n"; 

            std::set<std::string> unionSet;
            
            if(basic_block.getName() == "entry"){
                //errs() << "entry\n ";
                // if it is entry set caculated the in set based on liveout result
                for (auto& ueVar : UEVar_temp) {
                    //if (std::find(VarKill_temp.begin(), VarKill_temp.end(), ueVar) == VarKill_temp.end()) {
                        unionSet.insert(ueVar); 
                    //}
                }

                for (auto& liveOut : LiveOut_temp) {
                    if (std::find(VarKill_temp.begin(), VarKill_temp.end(), liveOut) == VarKill_temp.end()) {
                        unionSet.insert(liveOut); 
                    }
                }
                std::vector<std::string> Fun_INT(unionSet.begin(), unionSet.end());
                Func_In[string(F.getName())] = Fun_INT;
                Func_KillB[string(F.getName())] = VarKill_temp;
            }
        } 
}
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM) {
        auto &CG = MAM.getResult<CallGraphAnalysis>(M);
        FunctionAnalysisManager &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

        using VarSet = std::set<std::string>;
        std::unordered_map<std::string, VarSet> PointerUseSets;
        std::unordered_map<std::string, VarSet> PointerKillSets;


        for (Function &F : M) {
            // Get the alias analysis results for this function
            //errs() << "Processing function: " << F.getName().str() << "\n";

            // Skip analysis for certain functions if necessary
            if (F.isDeclaration() || F.isIntrinsic()) {
                errs() << "Skipping analysis for function: " << F.getName().str() << "\n";
                continue;
            }

            // Attempt to retrieve the alias analysis results for this function
            AAResults *AA = nullptr;
            try {
                AA = &FAM.getResult<AAManager>(F);
            } catch (const std::exception& e) {
                errs() << "Error retrieving alias analysis for function: " << F.getName().str() << " - " << e.what() << "\n";
                continue;
            }

            if (!AA) {
                errs() << "Alias analysis not available for function: " << F.getName().str() << "\n";
                continue;
            }
            int a = 0;
            for (auto &Arg : F.args()) {
                //llvm::errs() << "Parameter getty\n"; 
                llvm::Type *ArgType = Arg.getType();
                //llvm::errs() << "Parameter getty\n"; 
                // Generate a name or identifier for the argument
                std::string argName = Arg.hasName() ? Arg.getName().str() : "unnamed_arg";

                // Check if the argument type is a pointer
                if (ArgType->isPointerTy()) {
                    //llvm::errs() << "Parameter " << argName << " is a pointer.\n";
                    Pointer_Use[F.getName().str()].push_back(argName);
                    Pointer_Use[F.getName().str()].push_back(argName);
                } else {
                    llvm::errs() << "Parameter " << argName << " is not a pointer.\n";
                }
                ParameterPair parapair = {argName, a};
                Func_Para[F.getName().str()].push_back(parapair);
                a++;
            }
            //errs()<< "function name end: " << F.getName().str() << "\n";
            for (auto &BB : F) {
                for (auto &Inst : BB) {
                    //errs()<< "function name end: " << F.getName().str() << "\n";
                    if (auto *LoadInst = dyn_cast<llvm::LoadInst>(&Inst)) {
                        // Check aliasing with the first pointer
                        for (auto &OtherInst : BB) {
                            if (auto *OtherLoadInst = dyn_cast<llvm::LoadInst>(&OtherInst)) {
                                // Inside your loop where you analyze aliasing
                                if (LoadInst != OtherLoadInst) {
                                    AliasResult AR = AA->alias(MemoryLocation::get(LoadInst), MemoryLocation::get(OtherLoadInst));
                                    std::string pointer1Name = LoadInst->getPointerOperand()->hasName() ? LoadInst->getPointerOperand()->getName().str() : "<Unnamed Pointer>";
                                    std::string pointer2Name = OtherLoadInst->getPointerOperand()->hasName() ? OtherLoadInst->getPointerOperand()->getName().str() : "<Unnamed Pointer>";

                                    PointerPair pointers = {pointer1Name, pointer2Name};

                                    switch (AR) {
                                        case AliasResult::MayAlias:
                                            May_Alias[F.getName().str()].insert(pointers);
                                            llvm::errs() << "Inserted into May_Alias for function " << F.getName() << ": " << pointers.first << ", " << pointers.second << "\n";
                                            break;
                                        case AliasResult::MustAlias:
                                            Must_Alias[F.getName().str()].insert(pointers);
                                            llvm::errs() << "Inserted into Must_Alias for function " << F.getName() << ": " << pointers.first << ", " << pointers.second << "\n";
                                            break;
                                        default:
                                            // Handle default case if needed
                                            break;
                                    }

                                }

                            }
                        }
                        break;  // This 'break' will only analyze the first pair of LoadInsts. Remove it to analyze all pairs.
                    }
                }
            }
            for (auto &BB : F) {
                for (auto &Inst : BB) {
                    //errs()<< "function name123 end: " << F.getName().str() << "\n";
                    if (auto *StoreInst = dyn_cast<llvm::StoreInst>(&Inst)) {
                        std::string ptrName = StoreInst->getPointerOperand()->hasName() ? StoreInst->getPointerOperand()->getName().str() : "<Unnamed Pointer>";
                        std::string varName = StoreInst->getValueOperand()->hasName() ? StoreInst->getValueOperand()->getName().str() : "<Unnamed Var>";
                        Pointer_Kill[F.getName().str()].push_back(ptrName);
                    }
                }
            }

        }

        // Similarly for No_Alias, Partial_Alias, and Must_Alias
        // Iterate over all functions in the module, collecting callee-to-caller relationships
        std::map<Function *, std::set<Function *>> calleeToCallers;
        for (auto &CGNPair : CG) {
            CallGraphNode *CGN = CGNPair.second.get();
            Function *Caller = CGN->getFunction();
            if (!Caller || Caller->isDeclaration()) continue;

            for (auto &CallRecord : *CGN) {
                Function *Callee = CallRecord.second->getFunction();
                if (Callee && !Callee->isDeclaration()) {
                    calleeToCallers[Callee].insert(Caller);
                }
            }
        }

        // Now, print the call graph from callees to callers
        for (auto &Pair : calleeToCallers) {
            Function *Callee = Pair.first;
            auto &Callers = Pair.second;
            errs() << "Analyze Function: " << Callee->getName() << " is called by: ";
            for (Function *Caller : Callers) {
                errs() << Caller->getName() << " ";
            }
            errs() << "\n";
        }

        auto statesAreEqual = [](const auto& state1, const auto& state2) {
        if (state1.size() != state2.size()) return false;
        for (const auto& pair : state1) {
            const auto& key = pair.first;
            if (state2.find(key) == state2.end()) return false;
            if (state2.at(key) != pair.second) return false;
        }
        return true;
        };
        std::vector<std::vector<Function *>> callOrder;

        // The scc_iterator of CallGraph visits nodes of the graph in a topologically sorted order.
        for (auto &SCC : llvm::make_range(llvm::scc_begin(&CG), llvm::scc_end(&CG))) {
            std::vector<Function *> currentSCC;
            for (CallGraphNode *Node : SCC) {
                // Each node in the SCC represents a function, which may be null if it's an external node
                if (Node->getFunction() && !Node->getFunction()->isDeclaration()) {
                    currentSCC.push_back(Node->getFunction());
                }
            }
            if (!currentSCC.empty()) {
                callOrder.push_back(currentSCC);
            }
        }

        // Now, callOrder contains vectors of functions where each vector represents an SCC
        // SCCs are topologically sorted, but functions within an SCC are not because they are part of a cycle

        // Printing the functions based on call order
        //errs() << "Functions in call order respecting SCCs:\n";
        for (const auto &SCC : callOrder) {
            //errs() << "SCC: ";
            for (Function *F : SCC) {
                errs() << F->getName() << " ";
            }
            errs() << "\n";
        }
    int sb =0;        
    while (true) {
        sb++;
        // Store the previous state
        Func_KillB_Pre = Func_KillB;
        Func_In_Pre = Func_In;
        Func_Kill_Pre = Func_Kill;

        for (Function &F : M) {
            //std::string functionName = F.getName();
            visitor(F); // Analyze function (this should update Func_KillB, Func_In, Func_Kill)
        }

        // Check if any state has changed
        if (statesAreEqual(Func_KillB, Func_KillB_Pre) &&
            statesAreEqual(Func_In, Func_In_Pre) &&
            statesAreEqual(Func_Kill, Func_Kill_Pre)) {
            // No state has changed, we've reached a fixed point
            break;
        }
        if(sb>8)
        break;
    }

        errs() << "--------------------Final Result-------------------\n";
        errs() << "------------------UseVar in Function --------------\n";
        printFuncMapWithoutPointer(Func_In, "has UEV elements");
        errs() << "-----------------UsePointer in Function -----------\n";
        printFuncMapWithPointer(Func_In, "has LivePointer");
        errs() << "---------------KillVar in Function ----------------\n";
        printFuncMapWithoutPointer(Func_Kill, "has KILL elements");
        errs() << "---------------KillPointer in Function ----------------\n"; 
        printFuncMapWithPointer(Func_Kill, "has KILLPointer");
        return PreservedAnalyses::all();
    }
};
} // end anonymous namespace

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "CallGraphPass", LLVM_VERSION_STRING,
        [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM, ArrayRef<PassBuilder::PipelineElement>) {
                    if (Name == "callgraph-pass") {
                        MPM.addPass(CallGraphPass());
                        return true;
                    }
                    return false;
                }
            );
        }
    };
}

