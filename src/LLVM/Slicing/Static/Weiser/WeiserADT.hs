{-# LANGUAGE BangPatterns,DeriveGeneric,NoMonomorphismRestriction,
             ViewPatterns,TemplateHaskell,FlexibleContexts  #-}
 

module LLVM.Slicing.Static.Weiser.WeiserADT where

import GHC.Generics ( Generic )
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( makeLenses, (%~), (^.) )
import Control.Monad.RWS.Strict (RWS)
import qualified Control.Monad.RWS.Strict as RW

import Data.Map ( Map )
import qualified Data.Map as M
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import qualified Data.HashMap.Strict as HM 
import Data.Set ( Set )
import qualified Data.Set as S
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS
import Data.Maybe  
import Data.Monoid ( mempty )
import Data.List  

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CDG
import LLVM.Analysis.CallGraph

import LLVM.Slicing.Util.Utils
import LLVM.Slicing.Data.SliceType 



data SliceEnv = SEnv { succIdMap :: IntMap (HashSet Instruction)
                     , fModSet :: IntMap (HashSet Value)
--                     , callGr :: CallGraph 
                     , instCtrMap :: IntMap ValueIds
--                     , allRcMap :: IntMap ValueIds
                     }                      

data SliceState = SState { traces :: !Int 
--                         , instCtrMap :: IntMap ValueIds
                         } deriving (Generic)


data SliceInfo = SInfo { _sc :: ValueIds   
                       , _rcMap :: IntMap ValueIds
                       }
              deriving (Eq,Ord,Show,Generic)

$(makeLenses ''SliceInfo)

instance NFData SliceState where
  rnf = genericRnf

instance NFData SliceInfo where
  rnf = genericRnf

-------------
type Analysis = RWS SliceEnv String SliceState

runAnalysis :: RWS r b s a -> r -> s -> a 
runAnalysis a r s = fst $ RW.evalRWS a r s
analysisEnvironment = RW.asks
analysisGet = RW.get
analysisPut = RW.put
analysisLocal = RW.local

     
     
----------------------------------
------
getTrace :: Analysis Int 
getTrace = do {s <- analysisGet; return (traces s) }  

addTrace :: Instruction -> Analysis ()
addTrace i = do 
  s <- analysisGet  
  let tr' = 1 + traces s   
  analysisPut s { traces = tr'}


addRC :: SliceInfo -> Instruction -> ValueIds -> Analysis SliceInfo
addRC si i rc' = return $! addRC' si i rc'

addRC' :: SliceInfo -> Instruction -> ValueIds -> SliceInfo
addRC' si i rc' = (rcMap %~ IM.insertWith IS.union (instructionUniqueId i) rc') si

addRCs' :: SliceInfo -> [Instruction] -> ValueIds -> SliceInfo
addRCs' si is rc' = foldl' (\si' i -> addRC' si' i rc') si is

addRCatCallorExit :: SliceInfo -> Instruction -> Analysis SliceInfo
addRCatCallorExit si i = {-# SCC addRCatCallorExit #-}  do
--   cg <- analysisEnvironment callGr
--   rcm <- analysisEnvironment allRcMap
   let -- allFuns = mapMaybe getFunc . callValueTargets cg 
--       rcCall cargs = IS.unions. map (getRCatCall rcm cargs). allFuns
       addRcExit si cargs f = addRCs' si (functionExitInstructions f)
                                         (getRCatExit iSuccRC cargs f)
       Just iSucc = instructionSuccessor i   
       iID = instructionUniqueId i    
       iSuccRC = lkpRC si iSucc  
   case i of 
     CallInst {callFunction = fv, callArguments = (map fst -> args)} ->        
       case valueContent' fv of
         FunctionC f -> do
           let si' = addRcExit si args f
           addRC si' i $ getRCatCall args f  
         _ -> return si 
     InvokeInst {invokeFunction = fv, invokeArguments = (map fst -> args)} ->        
       case valueContent' fv of
         FunctionC f -> do
           let si' = addRcExit si args f
           addRC si' i $ getRCatCall args f  
         _ -> return si 
     _ -> return si
  where
    getExitValue :: Function -> Maybe Value   
    getExitValue f = 
        case functionExitInstruction f of
           Just RetInst {retInstValue = Just rv} -> Just rv   
           _ -> Nothing
    getRCatExit :: ValueIds -> [Value] -> Function -> ValueIds
    getRCatExit isuccRC cargs f  = IS.union fmlVars (isuccRC IS.\\ actVars) 
      where actVars = IS.fromList . map (valueUniqueId. fst) $ argMap'
            fmlVars = IS.fromList . map (valueUniqueId. snd) $ argMap'
            argMap = zip cargs (functionParameters f) 
            argMap' = filter (flip IS.member isuccRC . valueUniqueId. fst) argMap            
    getRCatCall :: [Value] -> Function -> ValueIds
    getRCatCall cargs f = IS.union actVars (entryRC IS.\\ fmlVars) 
      where entryRC = (lkpRC si funEntry) IS.\\ funInstIDs  
            funEntry = functionEntryInstruction f
            funInstIDs = IS.fromList . map instructionUniqueId $ functionInstructions f            
            actVars = IS.fromList . map (valueUniqueId. fst) $ argMap'
            fmlVars = IS.fromList . map (valueUniqueId. snd) $ argMap'
            argMap = zip cargs (functionParameters f) 
            argMap' = filter (flip IS.member entryRC . argumentUniqueId. snd) argMap
{-# INLINE addRCatCallorExit #-}

addSC :: SliceInfo -> Instruction -> Analysis SliceInfo
addSC si i = return $! (sc %~ IS.union (instRefs2 i) ) si

computeRC :: SliceInfo -> Instruction -> Analysis SliceInfo
computeRC si i = {-# SCC computeRC #-} do
   sidm <- analysisEnvironment succIdMap
   fms <- analysisEnvironment fModSet
--   rcm <- analysisEnvironment allRcMap
   let iSuccs = HS.toList $ IM.findWithDefault HS.empty iID sidm
       iID = valueUniqueId i
       rcs = IS.unions $ map (rc i) iSuccs
       rc i j = IS.union (rc2 i j) (rc1 i j)
       rc1 i j = (lkpRC si j) `IS.difference` (instDefs fms i) 
       rc2 i j = if isDD i j then instRefs2 i else IS.empty
       isDD i j = not . IS.null $ (lkpRC si j) `IS.intersection` (instDefs fms i)
   addRC si i rcs
{-# INLINE computeRC #-}

computeSC :: SliceInfo -> Instruction -> Analysis SliceInfo
computeSC si i = {-# SCC computeSC #-}  do 
  sidm <- analysisEnvironment succIdMap
  fms <- analysisEnvironment fModSet
--  rcm <- analysisEnvironment allRcMap
  let isSlice = or $ map (isDD i) iSuccs
      iSuccs = HS.toList $ IM.findWithDefault HS.empty iID sidm
      iID = valueUniqueId i
      isDD i j = not . IS.null $ (lkpRC si j) `IS.intersection` (instDefs fms i)
  if isSlice then addSC si i else return si
{-# INLINE computeSC #-}

updateRCSC :: SliceInfo -> Instruction -> Analysis SliceInfo
updateRCSC si i = {-# SCC updateRCSC #-} do
--  iInstCtr <- getInstCtr i
  icm <- analysisEnvironment instCtrMap
  let  -- infl b = IM.findWithDefault IS.empty (instructionUniqueId b) icm  
       -- isCD = not . IS.null $ (si ^. sc) `IS.intersection` iInstCtr     -- (infl i)
      iID = instructionUniqueId i
      isCD = IS.member iID. IS.unions. IM.elems $ IM.filterWithKey keyF icm
      keyF k _ = IS.member k (si ^. sc)
  if isCD then  addSC si i >>= \si' -> addRC si' i (instRefs2 i)
          else  return si
{-
 where
    getInstCtr i = do
        s <- analysisGet
        let iID = instructionUniqueId i
            instCtrM = instCtrMap s 
        case IM.lookup iID instCtrM of
          Just cis -> return cis
          Nothing -> do
            let cis = case i of
                 BranchInst {branchTrueTarget=tb,branchFalseTarget=fb} -> idsInBlks [tb,fb]
                 SwitchInst {switchDefaultTarget=db, switchCases=cases} -> idsInBlks (db: map snd cases)
                 IndirectBranchInst {indirectBranchTargets=bs} -> idsInBlks bs
                 _  -> IS.empty
            analysisPut s { instCtrMap = IM.insert iID cis instCtrM }
            return cis
    idsInBlks = IS.fromList . map instructionUniqueId . concatMap basicBlockInstructions
-}
{-# INLINE updateRCSC #-}

lkpRC ::  SliceInfo -> Instruction -> ValueIds
lkpRC si i = 
   IM.findWithDefault IS.empty (instructionUniqueId i) $ si ^. rcMap








