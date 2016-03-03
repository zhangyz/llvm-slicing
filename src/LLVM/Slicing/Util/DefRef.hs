{-# LANGUAGE BangPatterns,ViewPatterns,NoMonomorphismRestriction #-}


module LLVM.Slicing.Util.DefRef where

import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.IntMap.Strict ( IntMap )
import qualified Data.IntMap.Strict as IM  
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import qualified Data.IntSet as IS ( fromList )
import Data.Maybe 
import Data.List ( foldl' )
import Data.Tuple ( swap )
import Data.Hashable (Hashable)

import LLVM.Analysis

import LLVM.Slicing.Util.Mix
import LLVM.Slicing.Util.ValueTest



instDefs fms = hsToIS . valueDefs fms
instDDefs = hsToIS . directValueDefs
instRefs = IS.fromList . map valueUniqueId . directValueRefs
instRefs2 = hsToIS . valueRefs


valueDefs :: IsValue a => IntMap (HashSet Value) -> a -> HashSet Value
valueDefs fms iv = HS.delete (toValue iv). recursiveOp addValuesFrom. HS.singleton $ toValue iv  
 where 
  insert v q = if isConstant v then q else HS.insert v q
  addValuesFrom :: HashSet Value -> Value -> HashSet Value
  addValuesFrom q v =
   case valueContent' v of        
    InstructionC BranchInst {} -> q
    InstructionC SwitchInst {} -> q
    InstructionC IndirectBranchInst {} -> q
    InstructionC UnconditionalBranchInst { } -> q
    InstructionC RetInst {} -> q
    
    InstructionC StoreInst {storeAddress = ptr} -> insert (memAccessBase ptr) q        
    InstructionC AtomicRMWInst {atomicRMWPointer = ptr} -> insert (memAccessBase ptr) q
    InstructionC AtomicCmpXchgInst {atomicCmpXchgPointer = ptr} -> insert (memAccessBase ptr) q
    InstructionC InsertValueInst { insertValueAggregate = a} -> insert a q
    
    InstructionC CallInst {callFunction = cf, callArguments = (map fst -> args)} ->
         getCallInstDefs fms cf args q
    InstructionC InvokeInst {invokeFunction = cf, invokeArguments = (map fst -> args)} ->
         getCallInstDefs fms cf args q
--    InstructionC i -> case instructionFunction i of
--                Nothing -> q
--                Just iFun -> if i /= functionEntryInstruction iFun then q
--                             else foldl' (flip HS.insert) q (map toValue $ functionParameters iFun) 
    FunctionC f -> HS.union q mods 
         where  mods = IM.findWithDefault HS.empty (functionUniqueId f) fms   -- computeModSet f                
    _ -> q   -- insert (stripBitcasts v) q     
    
  getCallInstDefs :: IntMap (HashSet Value) -> Value -> [Value] -> HashSet Value -> HashSet Value
  getCallInstDefs fms fv args q = 
    case valueContent' fv of
      FunctionC f -> HS.union q mods  
        where  fID = functionUniqueId f 
               fFmls = map toValue $ functionParameters f
               mods = HS.union (HS.fromList . map fst $ argMap') 
                      (fMods `HS.difference` (HS.fromList . map snd $ argMap'))
               fMods = IM.findWithDefault HS.empty fID fms
               argMap = zip args fFmls 
               argMap' = filter (flip HS.member fMods . snd) argMap
      ExternalFunctionC ef -> if (isMemCMS ef || isC99Read ef)
                              then insert (memAccessBase $ args !! 0) q
                              else if isC99Scanf ef 
                                   then insert (memAccessBase $ args !! 1) q 
                                   else q
      _ -> q         
{-# INLINE valueDefs #-} 

--
directValueDefs = valueDefs2
valueDefs2 :: IsValue a => a -> HashSet Value
valueDefs2 iv = HS.delete (toValue iv). HS.filter (not . isConstant). 
                recursiveOp addValuesFrom. HS.singleton $ toValue iv  
 where 
  addValuesFrom :: HashSet Value -> Value -> HashSet Value
  addValuesFrom q v =
   case valueContent' v of        
    InstructionC BranchInst {} -> q
    InstructionC SwitchInst {} -> q
    InstructionC IndirectBranchInst {} -> q
    InstructionC UnconditionalBranchInst { } -> q
    InstructionC RetInst {} -> q
    
    InstructionC StoreInst {storeAddress = ptr} -> HS.insert (memAccessBase ptr) q        
    InstructionC AtomicRMWInst {atomicRMWPointer = ptr} -> HS.insert (memAccessBase ptr) q
    InstructionC AtomicCmpXchgInst {atomicCmpXchgPointer = ptr} -> HS.insert (memAccessBase ptr) q
    InstructionC InsertValueInst { insertValueAggregate = a} -> HS.insert a q
    
    InstructionC CallInst {callFunction = cf, callArguments = (map fst -> args)} ->
      if isMemCMS cf then HS.insert (memAccessBase $ args !! 0) q
      else q  --  HS.insert cf q   
    InstructionC InvokeInst {invokeFunction = cf, invokeArguments = (map fst -> args)} ->
      if isMemCMS cf then HS.insert (memAccessBase $ args !! 0) q
      else q 
--    FunctionC f -> HS.union funDDefs q
--      where  funDDefs = HS.filter (not . isLocalToFunction f). HS.unions . map valueDefs2 $ functionInstructions f
    _ -> q   -- HS.insert (stripBitcasts v) q          
{-# INLINE valueDefs2 #-} 

-----------
refs :: IsValue a => a -> [String]
refs = mapMaybe toVarName . HS.toList . refVals    -- HS.toList . valueRefs . toValue 
{-# INLINE refs #-}


refVals :: IsValue a => a -> HashSet Value
refVals = HS.filter (not . isConstant). valueRefs
{-# INLINE refVals #-}

valueRefs :: IsValue a => a -> HashSet Value
valueRefs = {-# SCC valueRefs #-}  
   recursiveOp addValuesFrom. HS.singleton . toValue 
  where 
    addValuesFrom :: HashSet Value -> Value -> HashSet Value
    addValuesFrom q v =
      case valueContent' v of        
        InstructionC StoreInst {storeValue = sv} -> HS.insert sv q
        InstructionC LoadInst {loadAddress = la} -> HS.insert (memAccessBase la) q
        InstructionC i@PhiNode {} -> foldl' (flip HS.insert) q vs
          where !vs = instructionOperands i ++ (maybeToList $ phi2Var v)
        InstructionC CallInst {callFunction = cf, callArguments = (map fst -> args)} ->
          if (isMemcpy cf || isMemmove cf)&& (length args >= 2) then 
             HS.insert (memAccessBase $ args !! 0) $ HS.insert (memAccessBase $ args !! 1) q
          else if isMemset cf then HS.insert (memAccessBase $ args !! 0) q
               else foldl' (flip HS.insert) q (args ++ returnValue cf)   -- (cf : args)
        InstructionC InvokeInst {invokeFunction = cf, invokeArguments = (map fst -> args)} ->
          if (isMemcpy cf || isMemmove cf) && (length args >= 2) then 
             HS.insert (memAccessBase $ args !! 0) $ HS.insert (memAccessBase $ args !! 1) q
          else if isMemset cf then HS.insert (memAccessBase $ args !! 0) q
               else foldl' (flip HS.insert) q (args ++ returnValue cf)   -- cf : args
        InstructionC i -> foldl' (flip HS.insert) q (instructionOperands i)
        FunctionC f -> foldl' (flip HS.insert) q (maybeToList $  funcExitValue f)  -- HS.union funRefs q        
--          where  funRefs = HS.filter (not . isLocalToFunction f). HS.unions . 
--                              map valueRefs $ functionInstructions f
        _ -> HS.insert (stripBitcasts v) q           
{-# INLINE valueRefs #-} 


directValueRefs :: IsValue a => a -> [Value]
directValueRefs iv = {-# SCC directValueRefs #-} filter (not. isConstant) $! 
  let v = toValue iv in
  case valueContent' v of        
    InstructionC StoreInst {storeValue = sv} -> sv : returnValue sv
    InstructionC LoadInst {loadAddress = la} -> [memAccessBase la]
--    InstructionC i@PhiNode {} -> instructionOperands i ++ (maybeToList $ phi2Var v)
    InstructionC CallInst {callFunction = cf, callArguments = (map fst -> args)} ->
      if (isMemcpy cf || isMemmove cf) && (length args >= 2) then 
         [memAccessBase $ args !! 0,memAccessBase $ args !! 1]
      else if isMemset cf then [memAccessBase $ args !! 0]
           else args ++ returnValue cf
    InstructionC InvokeInst {invokeFunction = cf, invokeArguments = (map fst -> args)} ->
      if (isMemcpy cf || isMemmove cf)&& (length args >= 2) then 
         [memAccessBase $ args !! 0,memAccessBase $ args !! 1]
      else if isMemset cf then [memAccessBase $ args !! 0]
           else args ++ returnValue cf
    InstructionC i -> instructionOperands i
    FunctionC f -> maybeToList $ funcExitValue f  
    _ -> [stripBitcasts v]            
{-# INLINE directValueRefs #-}


recursiveOp :: (Eq a, Hashable a) => (HashSet a -> a -> HashSet a) -> HashSet a -> HashSet a
recursiveOp addValuesFrom = {-# SCC recursiveOp #-} go HS.empty   -- . HS.singleton   
  where 
    go visited q
      | HS.null vals = visited
      | otherwise =
        let visited' = visited `HS.union` vals
            q' = foldl' addValuesFrom HS.empty (HS.toList vals)
        in go visited' q'
      where
        vals = HS.difference q visited
{-# INLINE recursiveOp #-}

---- 
inValRefs :: IsValue a => Value -> a -> Bool
inValRefs target v = target == memAccessBase (toValue v) 
                    || HS.member target (valueRefs v)

isVarRefs :: IsValue a => Value -> a -> Bool      
isVarRefs target v = toVarName' target `elem` refs v


-------
computeModSet :: [Function] -> IntMap (HashSet Value)
computeModSet = go IM.empty 
  where     
    fAliasMap = HM.fromList. map swap . getFunAlias'
    addFMods fms fs = foldl' (\fms' f -> addFunMod (fAliasMap f) fms' f) fms fs
    go fms funs = if fms' == fms then fms else go fms' funs
          where  fms' = addFMods fms funs  

addFunMod :: HashMap Value Value -> IntMap (HashSet Value) -> Function -> IntMap (HashSet Value)
addFunMod fAliasMap fms f = fms'
  where 
    fms' = IM.insertWith HS.union (functionUniqueId f) fMod fms
    fMod = getFunDefsOrRefs fAliasMap (valueDefs fms) f

functionRefs :: HashMap Value Value -> Function -> HashSet Value
functionRefs fAliasMap = HS.filter isValidVar . getFunDefsOrRefs fAliasMap valueRefs
  where  isValidVar v = case valueContent v of  
             ArgumentC _ -> True 
             GlobalVariableC _ -> True
             ExternalValueC _ -> True
             _  -> False

getFunDefsOrRefs :: HashMap Value Value -> (Instruction -> HashSet Value) -> Function -> HashSet Value
getFunDefsOrRefs fAliasMap defOrRef f = fDefsOrRefs
  where 
    fDefsOrRefs = addAlias. HS.filter fitF. HS.unions. map defOrRef $ fInsts 
    addAlias :: HashSet Value -> HashSet Value        
    addAlias vs = HS.union (HS.fromList. HM.elems $ HM.filterWithKey mapF fAliasMap) vs
          where mapF k _ = HS.member k vs
--    fAliasMap = HM.fromList. map swap $ getFunAlias' f
    fInsts = functionInstructions f
    fitF v = if hasExtraReference v then not (isLocalToFunction f v)
             else not (isLocalToFunction f v || isConstant v)
             



