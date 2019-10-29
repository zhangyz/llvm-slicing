{-# LANGUAGE NoMonomorphismRestriction #-}


module LLVM.Slicing.Util.ValueTest where

import LLVM.Analysis


-- Test for External Functions
isMemcpy = isExtFuns ["@llvm.memcpy.p0i8.p0i8.i32","@llvm.memcpy.p0i8.p0i8.i64"]
isMemmove = isExtFuns ["@llvm.memmove.p0i8.p0i8.i32","@llvm.memmove.p0i8.p0i8.i64"]
isMemset = isExtFuns ["@llvm.memset.p0i8.i32","@llvm.memset.p0i8.i64"]
isMemCMS = isExtFuns ["@llvm.memcpy.p0i8.p0i8.i32","@llvm.memcpy.p0i8.p0i8.i64",
                      "@llvm.memmove.p0i8.p0i8.i32","@llvm.memmove.p0i8.p0i8.i64",
                      "@llvm.memset.p0i8.i32","@llvm.memset.p0i8.i64" ]
isC99Scanf = isExtFuns ["@__isoc99_scanf"]    -- "@__isoc99_fscanf"
isC99Read = isExtFuns ["@fread","@_IO_getc","@gets"]


isExtFuns :: IsValue a => [String] -> a -> Bool
isExtFuns memFuns v  =
  case valueContent' (toValue v) of
    ExternalFunctionC ExternalFunction { externalFunctionName = fname } ->
      (show fname) `elem` memFuns
    _ -> False 



--- Test for a value of struct or array type
isAggregate :: (IsValue v) => v -> Bool              
isAggregate v = isGetElem v || isAggType v

isGetElem, isAggType :: (IsValue v) => v -> Bool
isGetElem v =  case valueContent' v of 
     InstructionC GetElementPtrInst {} -> True
     _ -> False
    
isAggType v =  case valueType v of
     TypeArray _ _ -> True
     TypeStruct _ _ _ -> True
     _ -> False    


----
isConstant :: Value -> Bool
isConstant v = case valueContent' v of
  ConstantC _ -> True
  _ -> False


hasExtraReference :: Value -> Bool
hasExtraReference v =  case valueContent v of   
  FunctionC f -> True
  InstructionC AllocaInst {} -> True
  GlobalVariableC _ -> True
  _  -> False


isGlobal :: Value -> Bool
isGlobal v = case valueContent v of
  GlobalVariableC _ -> True
  ExternalValueC _ -> True
  _ -> False


isLocalToFunction :: IsValue a => Function -> a -> Bool
isLocalToFunction f v = case valueContent v of
    FunctionC f0 -> f == f0
--    ArgumentC a -> argumentFunction a == f
    BasicBlockC b -> basicBlockFunction b == f
    InstructionC i -> instructionFunction i == Just f
    _ -> False

isCtrInst :: Instruction -> Bool
isCtrInst i = case i of
    BranchInst {} -> True
    SwitchInst {} -> True
    IndirectBranchInst {} -> True
--    UnconditionalBranchInst {} -> True
    _  -> False

isCallInst :: Instruction -> Bool
isCallInst CallInst {} = True
isCallInst InvokeInst {} = True
isCallInst _ = False  
         

isAllocaInst :: Instruction -> Bool
isAllocaInst AllocaInst {} = True
isAllocaInst _ = False

isConstantValue :: Value -> Bool
isConstantValue v =  case valueContent' v of
    ConstantC ConstantPointerNull {} -> True
    ConstantC ConstantValue {} -> True
    _ -> False
    
isExtFunction :: IsValue a => a -> Bool
isExtFunction v  =
  case valueContent' (toValue v) of
    ExternalFunctionC _ -> True
    _ -> False 

isBBEntryInst :: Instruction -> Bool
isBBEntryInst i = 
  case instructionBasicBlock i of
    Nothing -> False
    Just iBB -> [i] == (take 1 $ basicBlockInstructions iBB)

isFunEntryInst :: Instruction -> Bool
isFunEntryInst i = 
  case instructionFunction i of
    Nothing -> False
    Just iFun -> i == functionEntryInstruction iFun  
