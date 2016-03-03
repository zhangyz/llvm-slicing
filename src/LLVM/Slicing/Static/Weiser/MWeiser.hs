{-# LANGUAGE BangPatterns,ViewPatterns,DeriveGeneric,RankNTypes,TemplateHaskell #-}
 

module LLVM.Slicing.Static.Weiser.MWeiser (
 -- * Types
 SliceSummary(..),
 -- * Slice Computing
 computeSlice,
 genSliceTable, genSliceTable2
 )
 where

import Control.Arrow 
import GHC.Generics ( Generic )
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Lens', makeLenses, (.~), (%~), (^.) )

import Data.Map ( Map )
import qualified Data.Map as M
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.Set ( Set )
import qualified Data.Set as S
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS
import Data.Maybe 
import Data.Monoid 
import Data.List  
import Data.Char ( isLetter )
--import qualified Data.Text as T ( unpack )

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow
import LLVM.Analysis.CallGraph
import LLVM.Analysis.PointsTo
import LLVM.Analysis.PointsTo.TrivialFunction
--import LLVM.Analysis.PointsTo.Andersen

import LLVM.Slicing.Util.Utils
import LLVM.Slicing.Data.SliceType
import LLVM.Slicing.Static.Weiser.WeiserADT


------
data SliceSummary =
  SliceSummary {  _bwdSlice :: IntSet  
                , _rcSummary :: IntMap IntSet     
                , _traceSize :: Int
                }
  deriving (Generic)

$(makeLenses ''SliceSummary)

instance Eq SliceSummary where
  (SliceSummary s1 r1 _) == (SliceSummary s2 r2 _) = s1 == s2 && r1 == r2

instance Monoid SliceSummary where
  mempty = SliceSummary mempty mempty 0
  mappend (SliceSummary bs1 ms1 tr1) (SliceSummary bs2 ms2 tr2) =
    SliceSummary (IS.union bs2 bs1)(IM.unionWith IS.union ms1 ms2)(tr1 + tr2)

instance NFData SliceSummary where
  rnf = genericRnf


--
data SliceAnalysis = SliceAnalysis { _sliceSumm :: SliceSummary }
  deriving (Eq, Generic)

$(makeLenses ''SliceAnalysis)

instance NFData SliceAnalysis where
  rnf = genericRnf

instance Monoid SliceAnalysis where
  mempty = SliceAnalysis { _sliceSumm = mempty }
  mappend a1 a2 =
    SliceAnalysis { _sliceSumm = _sliceSumm a1 `mappend` _sliceSumm a2 }


top :: SliceInfo
top = SInfo mempty mempty  


meetSliceInfo :: SliceInfo -> SliceInfo -> SliceInfo
meetSliceInfo (SInfo sc1 rc1) (SInfo sc2 rc2) = {-# SCC meetSliceInfo #-}
    SInfo (IS.union sc1 sc2)(IM.unionWith IS.union rc1 rc2)
{-# INLINE meetSliceInfo #-}

sliceTransfer :: SliceInfo -> Instruction -> Analysis SliceInfo
sliceTransfer si i =  {-# SCC sliceTransfer #-}  do  
      addTrace i
      !si1 <- computeRC si i
      !si2 <- computeSC si1 i
      !si3 <- updateRCSC si2 i
      addRCatCallorExit si3 i
{-# INLINE sliceTransfer #-}

identifySlice ::    
       (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
        => [Value] -> Module -> Lens' compositeSummary SliceSummary
        -> ComposableAnalysis compositeSummary funcLike
identifySlice vs m lns =  
  composableAnalysisM runner (sliceAnalysis funMap vs) lns
  where
    runner a = runAnalysis a constData cache
    constData = SEnv mempty funModSets mempty 
    cache = SState 0      
    funModSets = computeModSet fs 
    fs = moduleDefinedFunctions m
    funMap = IM.fromList [(valueUniqueId f, (succIdM f, genCtrDepMap f))| f <- fs]
    succIdM f = IM.fromList [(valueUniqueId i,toSuccIds i)| i <- functionInstructions f ]
       where  toSuccIds = HS.fromList. instructionSuccessors cfg
              cfg = controlFlowGraph f 

sliceAnalysis :: (FuncLike funcLike,HasCFG funcLike,HasFunction funcLike)
               => IntMap (IntMap (HashSet Instruction), IntMap ValueIds) -> 
                  [Value] -> funcLike -> SliceSummary -> Analysis SliceSummary
sliceAnalysis funM vs funcLike s@(SliceSummary sc rcm _) = do  
  let envMod e = e { succIdMap = fSuccIdM   
                   , instCtrMap = fInstCtrM 
--                   , allRcMap = rcm
                   } 
      (fSuccIdM,fInstCtrM) = IM.findWithDefault mempty fID funM
      top0 = SInfo sc rcm
      !fact0 = foldl' initRC top0 vs
      initRC si v = 
          case valueFunction v of 
             Just fn -> addRCs' si (functionExitInstructions fn) (vIDs v)
             Nothing -> if fName /= "main" then si
                        else addRCs' si (functionExitInstructions f) (vIDs v)
      vIDs v = IS.singleton $ valueUniqueId v
      analysis = bwdDataflowAnalysis top meetSliceInfo sliceTransfer  
  localInfo <- analysisLocal envMod (dataflow funcLike analysis fact0)  
  tr <- getTrace 
  let si@(SInfo sc' rcm') = dataflowResult localInfo
  return $ (bwdSlice .~ sc')
         $ (traceSize %~ (+) tr)
         $! (rcSummary %~ IM.unionWith IS.union rcm') s   
  where
    f = getFunction funcLike  
    fID = functionUniqueId f              
    fName = identifierAsString (functionName f)      
    

computeSlice :: Module -> [Value] -> SliceSummary
computeSlice m vs = res  -- `showGraph` (cg,mName)
  where
    cg = callGraph m pta []
    funs = callGraphFunctions cg     
    pta = runPointsToAnalysis m
    funModSets = computeModSet funs   
    res = callGraphAnalysisM runner (sliceAnalysis funMap vs) funs mempty
    runner a = runAnalysis a constData cache
    constData = SEnv mempty funModSets mempty 
    cache = SState 0   
--    instCtrM = genInstCtrMap m
    funMap = IM.fromList [(valueUniqueId f, (succIdM f, genCtrDepMap f))| f <- funs]
    succIdM f = IM.fromList [(valueUniqueId i,toSuccIds i)| i <- functionInstructions f ]
       where  toSuccIds = HS.fromList. instructionSuccessors cfg
              cfg = controlFlowGraph f 
    


-------
genSliceTable2 :: Module -> (Map String [String],Map String [String])
genSliceTable2 m = (toSrcLns bwdST, error "MWeiser's forward slicing is not available!")
  where (bwdST,fwdST) = genSliceTable m
        valMap = genValueMap m
        toSrcLns = M.map (toSrcLnStr valMap)

genSliceTable :: Module -> (SliceTable,SliceTable)    
genSliceTable m = (bwdSlices, error "MWeiser's forward slicing is not available!")
--            `debug` trStr
  where summarys = map (computeSlice m. addAlias aliasMap) allVals'
        bwdSlices = M.fromList. zip vars $! map _bwdSlice summarys  
        fs = moduleDefinedFunctions m     
        allVals =  map toValue (concatMap functionParameters fs)
                ++ map toValue (moduleGlobalVariables m) 
                ++ map toValue (concatMap funcAllocInsts fs)
        allVals' = filter ((\(k:_)->(isLetter k || k == '_')). drop 1. toVarName') allVals
        vars = map (drop 1 . toVarName') $ allVals'
        aliasMap = genAliasMap' m
        trStr = "\n\tIts trace Info: #Insts_Weiser = " ++ show (sum $ map _traceSize summarys)

addAlias :: HashMap Value Value -> Value -> [Value]        
addAlias am v = v : (maybeToList $ HM.lookup v am)






