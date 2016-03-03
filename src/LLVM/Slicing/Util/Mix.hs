{-# LANGUAGE NoMonomorphismRestriction #-}

module LLVM.Slicing.Util.Mix where


import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS ( fromList )
import Data.Maybe 
import Data.List 
import Data.Char ( isDigit )

import LLVM.Analysis
import LLVM.Analysis.CFG 

import LLVM.Slicing.Util.ValueTest  ( isConstant,isAllocaInst )


--------
type ValueIds = IntSet
type ValueId = Int

hsToIS :: IsValue a => HashSet a -> ValueIds
hsToIS = IS.fromList . HS.toList . HS.map valueUniqueId 


--
returnValue :: IsValue a => a -> [Value]
returnValue fv = maybeToList $ do
   f <- getFunc (toValue fv) 
   rv <- funcExitValue f
   return rv
     
funcExitValue :: Function -> Maybe Value
funcExitValue f = 
   case functionExitInstruction f of
      Just i@RetInst {retInstValue = Just rv} -> 
         if isConstant rv then Nothing else Just rv
      _ -> Nothing

getFunc :: Value -> Maybe Function
getFunc v = case valueContent v of   
       FunctionC f -> Just f
       _  -> Nothing  


--
phi2Var :: IsValue a => a -> Maybe Value
phi2Var pv = {-# SCC phi2Var #-}  case valueContent' (toValue pv) of 
   InstructionC PhiNode {phiIncomingValues = pvs} ->
     case partition (isConstant . fst) pvs of 
       ([],[]) -> Nothing
       (vs,[]) -> listToMaybe2 $ mapMaybe getVar vs
       (_, vs) -> listToMaybe2 $ mapMaybe getVar vs 
   _ -> Nothing
   where
      getVar (val,lab) = let ls = lkpVars val lab in
        if not (null ls) then listToMaybe2 ls
        else case valueContent' val of
          InstructionC LoadInst {loadAddress = la} -> Just la
          _ -> Nothing 
      lkpVars v = mapMaybe (matchVar v). basicBlockInstructions. toBB 
      listToMaybe2 ls = case nub ls of
          [v] -> Just v   
          _   -> Nothing  
      matchVar v i = case i of 
        StoreInst {storeValue = sv, storeAddress = sa} ->
           if sv == v then Just sa else Nothing
        _ -> Nothing
      toBB v = case valueContent v of
        BasicBlockC bb -> bb
        _ -> error ("Expected basic block: " ++ show v)
{-# INLINE phi2Var #-}        



---- 
vEq = valueEq
valueEq :: (IsValue a,Eq a) => a -> a -> Bool
valueEq v1 v2 = (v1 == v2) || (toVarName' v1 == toVarName' v2) 
        
toValName, toVarName' :: IsValue a => a -> String
toValName v = maybe (valStr v) show (valueName v)
  where valStr v = "_" ++ show (valueUniqueId v)

toVarName' val = fromMaybe (toValName val) . toVarName $ toValue val
{-# INLINE toVarName' #-}
 
toVarName :: Value -> Maybe String
toVarName val =
  case valueContent' val of
    GlobalVariableC gv -> Just $ show (globalVariableName gv)
    InstructionC i@AllocaInst {} -> Just $ instName i    
    ArgumentC av -> Just $ argName av
    GlobalAliasC ga -> Just $ show (globalAliasName ga)
--    InstructionC i@PhiNode {} -> liftM show (valueName i)    
    _ -> Nothing   
  where  
    instName i = maybe (instIdStr i) show (instructionName i) ++ 
                 maybe "@**" (show . functionName) (instructionFunction i)
    instIdStr i = "_" ++ show (instructionUniqueId i)
    argName av = show (argumentName av) ++ (show . functionName $ argumentFunction av)
{-# INLINE toVarName #-} 


---
getFunAlias :: Function -> [(String,String)]
getFunAlias = mapBoth toVarName' toVarName'. getFunAlias'


getFunAlias' :: Function -> [(Value,Value)]
getFunAlias' = mapMaybe getInstAlias. functionInstructions
  where
    getInstAlias :: Instruction -> Maybe (Value,Value)
    getInstAlias i = do
      (ptr,sv) <- getStoreInstInfo i
      argVal <- getArgVal sv
      ptrVal <- getAllocVal ptr
      return (argVal, ptrVal)
    --    
    getStoreInstInfo i = case i of 
      StoreInst {storeAddress = ptr, storeValue = sv} -> Just (ptr,sv)
      _  -> Nothing     
    getArgVal v = case valueContent' v of 
      GlobalVariableC _ -> Just v 
      GlobalAliasC _ -> Just v
      ArgumentC av -> if elem av (functionParameters $ argumentFunction av) 
                      then Just v     
                      else Nothing
      _  -> Nothing
    getAllocVal v = case valueContent' v of 
      InstructionC i@AllocaInst {} ->
          if isTempVar i then Just v else Nothing
         where  isTempVar = maybe False (isDigit. head. drop 1. show). valueName
      _ -> Nothing   
{-# INLINE getFunAlias' #-} 


----------------------------
funcAllocInsts :: Function -> [Instruction]
funcAllocInsts f = allocInsts
  where  allocInsts = filter isAllocaInst $ functionInstructions f


--
instructionSuccessor :: Instruction -> Maybe Instruction
instructionSuccessor i =
  case rest of
    _:nxt:_ -> Just nxt
    _ -> Nothing
  where
    Just bb = instructionBasicBlock i
    rest = dropWhile (/=i) (basicBlockInstructions bb)

instSuccs = instructionSuccessors
instructionSuccessors :: CFG -> Instruction -> [Instruction]
instructionSuccessors cfg i =
  if i == ti 
  then map blockEntryInst bs 
  else [rest !! 1]
  where
    Just bb = instructionBasicBlock i
    ti = basicBlockTerminatorInstruction bb
    bs = basicBlockSuccessors cfg bb
    rest = dropWhile (/=i) (basicBlockInstructions bb)
    blockEntryInst = head . basicBlockInstructions

instructionPredecessors :: CFG -> Instruction -> [Instruction]
instructionPredecessors cfg i =
  if instructionIsEntry i  
  then map basicBlockTerminatorInstruction ps 
  else [last rest]
  where
    Just bb = instructionBasicBlock i
    ps = basicBlockPredecessors cfg bb
    rest = takeWhile (/=i) (basicBlockInstructions bb)


----
--

mapFsts :: (a -> b) -> [(a,c)] -> [(b,c)]
mapFsts f = mapBoth f id

mapSnds :: (a -> b) -> [(c,a)] -> [(c,b)]
mapSnds g = mapBoth id g

mapBoth :: (a -> a') -> (b -> b') -> [(a,b)] -> [(a',b')]
mapBoth f g xs = [(f x, g y) | (x,y) <- xs]

sortFst :: Ord a => [(a,b)] -> [(a,b)]
sortFst = sortBy (\(x,_) (y,_) -> compare x y)

groupFst :: Eq a => [(a, t)] -> [[(a, t)]]
groupFst = groupBy (\(x,_) (y,_) -> x == y) 



             
---------------------------------------------------------------------
--- Citing from LLVM.Analysis
memAccessBase :: Value -> Value
memAccessBase ptr =
  case valueContent' ptr of
    GlobalVariableC gv -> toValue gv
    InstructionC i@AllocaInst {} -> toValue i
    ArgumentC a -> toValue a
    InstructionC LoadInst { loadAddress = la } -> stripBitcasts la
    InstructionC GetElementPtrInst { getElementPtrValue = base } ->
      memAccessBase base
--    InstructionC PhiNode { phiIncomingValues = pvs } -> ...
    _ -> stripBitcasts ptr

allValues :: Module -> [Value]
allValues m = allVals
  where
    fs = moduleDefinedFunctions m
    allArgs = concatMap functionParameters fs
    allBlocks = concatMap functionBody fs
    allInsts = concatMap basicBlockInstructions allBlocks
    allVals = concat [ map toValue fs
                     , map toValue (moduleGlobalVariables m)
                     , map toValue (moduleExternalValues m)
                     , map toValue (moduleExternalFunctions m)
                     , map toValue (moduleAliases m)
                     , map toValue allBlocks
                     , map toValue allInsts
                     , map toValue allArgs
                     ]


