{-# LANGUAGE TypeSynonymInstances,MultiParamTypeClasses,FlexibleContexts #-}
 

module LLVM.Slicing.Static.SDG.IFDS.SummaryEdge (
 -- * Types
 SDGSummEdge(..),
 SummEdgeMap,
 -- * Computing Summary Edge 
 genSummEdgeMap,
 extractSummEdges,
 runIFDS,
 -- * Citing from LLVM.Analysis.ICFG 
 mkICFG
 ) where


import Control.Monad.State ( execState )
import qualified Data.Map as M
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Char ( isLetter )
import Data.Graph.Inductive  ( lab )

import LLVM.Analysis

import LLVM.Slicing.Util.Utils

-- Based on the IFDS algorithm which is not directly import from LLVM.Analysis, 
--    but it could be found from its github website as follows.
--    https://github.com/travitch/llvm-analysis/blob/master/src/LLVM/Analysis/IFDS.hs
import LLVM.Analysis.IFDS
import LLVM.Analysis.ICFG 
import LLVM.Analysis.Internal.Worklist ( worklistFromList )


----------------------------------------------------------
---- Compute SDG's Summary Edges based on the IFDS method
---
data SDGSummEdge = SDGSummEdge (IntMap Value)  
type SummEdgeMap  = IntMap (Set (ValueId,ValueId))

instance IFDSAnalysis SDGSummEdge ValueId where
  flow = summFlow
  callFlow = summCallFlow
  passArgs = summPassArgs
  externPassArgs = summExternPassArgs
  returnVal = summReturnVal
  externReturnVal = summExternReturnVal
  entrySetup = summEntrySetup

storeFlow :: IntMap Value -> ValueId -> Instruction -> (Value,Value) -> [Maybe ValueId]
storeFlow vm v' i (sa,sv) 
  | valueEq (vm ^! v') sa  = [Just (valueUniqueId sa)]   
  | inValRefs (vm ^! v') sv = [Just v',Just (valueUniqueId sa)]    
  | otherwise = [Just v']  
  
summFlow :: SDGSummEdge -> Maybe ValueId -> Instruction -> [CFGEdge] -> [Maybe ValueId]
summFlow (SDGSummEdge vm) v@(Just v') i@StoreInst {storeAddress = sa, storeValue = sv} _
  = storeFlow vm v' i (sa,sv)
summFlow (SDGSummEdge vm) v@(Just v') i@AtomicRMWInst {atomicRMWPointer = sa, atomicRMWValue = sv} _
  = storeFlow vm v' i (sa,sv)
summFlow (SDGSummEdge vm) v@(Just v') i@AtomicCmpXchgInst {atomicCmpXchgPointer = sa, atomicCmpXchgNewValue = sv} _
  = storeFlow vm v' i (sa,sv)
summFlow (SDGSummEdge vm) v@(Just v') i@InsertValueInst {insertValueAggregate = sa, insertValueValue = sv} _ 
--  | isVarRefs v' sa  = [v,Just (valueUniqueId sa)]
  | inValRefs (vm ^! v') i = [v,Just (valueUniqueId sa)]
  | otherwise = [v]  
summFlow (SDGSummEdge vm) v _ _  = [v]


summCallFlow :: SDGSummEdge -> Maybe ValueId -> Instruction -> [CFGEdge] -> [Maybe ValueId]
summCallFlow _ Nothing _ _ = [Nothing]
summCallFlow (SDGSummEdge vm) v@(Just v') _ _ = 
  case isGlobal (vm ^! v') of
    True -> []   
    _ -> [v]

summPassArgs :: SDGSummEdge -> Maybe ValueId -> Instruction -> Function -> [Maybe ValueId]
summPassArgs (SDGSummEdge vm) Nothing i@(CallInst {callArguments = cargs}) f = 
  Nothing : map (Just. valueUniqueId. toValue) (functionParameters f)
summPassArgs (SDGSummEdge vm) Nothing i@(InvokeInst {invokeArguments = cargs}) f =  
  Nothing : map (Just. valueUniqueId. toValue) (functionParameters f)
summPassArgs _ Nothing _ _ = [Nothing]
summPassArgs (SDGSummEdge vm) v@(Just v') i@(CallInst {callArguments = cargs}) f =
  case isGlobal (vm ^! v') of
    True -> v : map (Just . valueUniqueId. snd) args 
    False -> map (Just . valueUniqueId. snd) args 
  where
    argMap = zip (map fst cargs) (functionParameters f)
    args = filter (inValRefs (vm ^! v') . fst) argMap 
summPassArgs (SDGSummEdge vm) v@(Just v') i@(InvokeInst {invokeArguments = cargs}) f =
  case isGlobal (vm ^! v') of
    True -> v : map (Just . valueUniqueId. snd) args 
    False -> map (Just . valueUniqueId. snd) args 
  where
    argMap = zip (map fst cargs) (functionParameters f)
    args = filter (inValRefs (vm ^! v') . fst) argMap 
summPassArgs _ v@(Just v') _ f = [v]

summExternPassArgs :: SDGSummEdge -> Maybe ValueId -> Instruction -> Maybe ExternalFunction -> [Maybe ValueId]
summExternPassArgs _ Nothing _ _ = [Nothing]
summExternPassArgs (SDGSummEdge vm) v@(Just v') i _ = globalProp
  where  globalProp = if isGlobal (vm ^! v') then [v] else []

summReturnVal :: SDGSummEdge -> Maybe ValueId -> Instruction -> Instruction -> [Maybe ValueId]
summReturnVal (SDGSummEdge vm) Nothing _ ci = [Nothing]
summReturnVal (SDGSummEdge vm) v@(Just v') ri@(RetInst{}) ci@(CallInst {callArguments = cargs}) = 
   map (Just . valueUniqueId. fst) args ++ globalProp
  where  
    globalProp = if isGlobal (vm ^! v') then [v] else []  
    Just f = instructionFunction ri  
    argMap = zip (map fst cargs) (functionParameters f)
    args = filter (inValRefs (vm ^! v') . snd) argMap
summReturnVal (SDGSummEdge vm) v@(Just v') ri@(RetInst{}) ci@(InvokeInst {invokeArguments = cargs}) = 
   map (Just . valueUniqueId. fst) args ++ globalProp
  where  
    globalProp = if isGlobal (vm ^! v') then [v] else []  
    Just f = instructionFunction ri  
    argMap = zip (map fst cargs) (functionParameters f)
    args = filter (inValRefs (vm ^! v') . snd) argMap
summReturnVal _ _ _ _ = []

summExternReturnVal :: SDGSummEdge -> Maybe ValueId -> Maybe ExternalFunction -> Instruction -> [Maybe ValueId]
summExternReturnVal (SDGSummEdge vm) Nothing _ ci = [Nothing]
summExternReturnVal (SDGSummEdge vm) v@(Just v') _ ci  = 
  case inValRefs (vm ^! v') ci of
    True -> v : globalProp
    False -> globalProp
  where  globalProp = if isGlobal (vm ^! v') then [v] else []


summEntrySetup :: SDGSummEdge -> Module -> Function -> [Maybe ValueId]
summEntrySetup (SDGSummEdge vm) m _ = Nothing : map (Just. valueUniqueId. toValue) glbs 
 where
  glbs = filter((\(k:_)->(isLetter k || k == '_')). drop 1. toVarName')(moduleGlobalVariables m)
              


----------------------------------------------------------------
---
genSummEdgeMap :: IFDSAnalysis a ValueId => a -> ICFG -> SummEdgeMap
genSummEdgeMap a g = extractSummEdges $ runIFDS a g  

runIFDS :: IFDSAnalysis a ValueId => a -> ICFG -> IFDS a ValueId
runIFDS analysis g = finalState
  where
    initialEdges = concatMap (mkInitialEdges analysis (icfgModule g)) (icfgEntryPoints g)
    initialState = IFDS { pathEdges = S.fromList initialEdges
                        , summaryEdges = S.empty
                        , ifdsWorklist = worklistFromList initialEdges
                        , incomingNodes = M.empty
                        , endSummary = M.empty
                        , entryValues = M.empty
                        , summaryValues = M.empty
                        , icfg = g
                        , ifdsAnalysis = analysis
                        }
    finalState = execState tabulate initialState

extractSummEdges :: IFDSAnalysis a ValueId => IFDS a ValueId -> SummEdgeMap
extractSummEdges s = S.foldr' populatePE IM.empty ps
  where
    ps = pathEdges s
    g = (icfgGraph . icfg) s
    populatePE (PathEdge (Just d1) n (Just d2)) m =
      case isExitNode n of
        False -> m
        True -> IM.insert nFunc newSet m
          where
            Just nFunc = nodeToFunction n
            newSet = case IM.lookup nFunc m of
                Nothing -> S.singleton (d1,d2)
                Just vals -> S.insert (d1,d2) vals
    populatePE _ m = m 
    nodeToFunction n = do
      (InstNode i) <- lab g n
      f <- instructionFunction i
      return $ valueUniqueId f
    isExitNode n = case lab g n of
      Just (InstNode i) -> isRetInst i   
      _ -> False
      where
        isRetInst RetInst {} = True
        isRetInst _ = False

 
