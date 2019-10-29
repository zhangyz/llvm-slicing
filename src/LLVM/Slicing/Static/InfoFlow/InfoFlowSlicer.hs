{-# LANGUAGE BangPatterns,ViewPatterns,DeriveGeneric,TypeSynonymInstances,
             RankNTypes,MultiParamTypeClasses,TemplateHaskell #-}
 

module LLVM.Slicing.Static.InfoFlow.InfoFlowSlicer (
 -- * Types
 SliceSummary(..),
 -- * Slice Computing
 computeSlice,
 genSliceTable, genSliceTable2,
 getSliceTable
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
import qualified Data.HashMap.Strict as HM ( fromList )
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS
import Data.Tuple ( swap )
import Data.Maybe 
import Data.Monoid 
import Data.List  
import Data.Char ( isLetter )
import qualified Data.Text as T ( unpack )
import Text.Printf ( printf )
import qualified Data.Graph.Inductive as G
import qualified Data.Relation as R

import LLVM.Analysis
import LLVM.Analysis.CFG  hiding (CFGEdge(..))
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow
import LLVM.Analysis.CallGraph
import LLVM.Analysis.PointsTo
import LLVM.Analysis.PointsTo.TrivialFunction
--import LLVM.Analysis.PointsTo.Andersen

import LLVM.Slicing.Util.Utils
import LLVM.Slicing.Data.SliceType        
import LLVM.Slicing.Static.InfoFlow.InfoFlowADT


--import Debug.Trace ( trace )

------
data SliceSummary =
  SliceSummary {  _funInfoRel :: IntMap InfoFlowRel    
                , _funSummEdges :: IntMap (R.Rel String String)  
                , _traceSize :: Int
                }
  deriving (Generic)

$(makeLenses ''SliceSummary)

instance Eq SliceSummary where
  (SliceSummary ir1 s1 tr1) == (SliceSummary ir2 s2 tr2) = 
         ir1 == ir2 && s1 == s2       -- && tr1 == tr2

instance Monoid SliceSummary where
  mempty = SliceSummary mempty mempty 0
  mappend (SliceSummary ir1 se1 tr1) (SliceSummary ir2 se2 tr2) =
    SliceSummary (IM.unionWith mrgInfoRel ir1 ir2)(IM.unionWith S.union se1 se2)(tr1 + tr2)

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

---------------
----
top :: SliceInfo
top = SInfo mempty mempty mempty mempty mempty  


meetSliceInfo :: SliceInfo -> SliceInfo -> SliceInfo
meetSliceInfo (SInfo vi1 iv1 vv1 ds1 ps1) (SInfo vi2 iv2 vv2 ds2 ps2) =
           SInfo (IM.unionWith S.union vi1 vi2)(IM.unionWith S.union iv1 iv2)
                 (IM.unionWith S.union vv1 vv2)(IM.unionWith S.union ds1 ds2)
                 (IM.unionWith S.union ps1 ps2)

sliceTransfer :: SliceInfo -> Instruction -> Analysis SliceInfo
sliceTransfer si i =    do   -- dbgIt i $  
   addTrace i
   case i of    
--     StoreInst {storeValue = sv} -> getInfoRel sv iDefs fVars
--     AtomicRMWInst {atomicRMWValue = av} -> getInfoRel av iDefs fVars
--     AtomicCmpXchgInst {atomicCmpXchgNewValue = nv} -> getInfoRel nv iDefs fVars          
--     InsertValueInst {insertValueValue = iv} -> getInfoRel iv iDefs fVars        
         
     BranchInst {branchCondition=c,branchTrueTarget=tb,branchFalseTarget=fb} -> 
       doBrInfo si i [tb,fb]
     SwitchInst {switchValue=v,switchDefaultTarget=db, switchCases=cases} -> 
       doBrInfo si i (db: map snd cases)
     IndirectBranchInst {indirectBranchAddress=a,indirectBranchTargets=bs} -> 
       doBrInfo si i bs 
--     UnconditionalBranchInst {unconditionalBranchTarget=b} ->  
--       doUnBrInfo si i (basicBlockTerminatorInstruction b)
       
     CallInst { callFunction = fv, callArguments = avs } ->   
       doCallInfo si i fv (map fst avs) 
     InvokeInst { invokeFunction = fv, invokeArguments = avs } ->
       doCallInfo si i fv (map fst avs) 
       
     _ -> computeInfoRel si i  
{-# INLINE sliceTransfer #-}   


identifySlice ::    
       (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
        => Module -> CallGraph -> Lens' compositeSummary SliceSummary
        -> ComposableAnalysis compositeSummary funcLike
identifySlice m cg lns =  
  composableAnalysisM runner (sliceAnalysis m cg) lns
  where
    runner a = runAnalysis a constData cache
    constData = SEnv undefined undefined mempty mempty mempty
    cache = SState 0 mempty

sliceAnalysis :: (FuncLike funcLike, HasCFG funcLike,HasFunction funcLike)
               => Module -> CallGraph -> funcLike -> SliceSummary -> Analysis SliceSummary
sliceAnalysis m cg funcLike s@(SliceSummary irM seM _) = do   
  let envMod e = e { fCFG = controlFlowGraph f
                   , callGr = cg
                   , summEdges = seM
                   , fInfoRels = irM
                   , fAllVars = fVars } 
      infoR0 = (mempty,mempty,mempty,fVV0) 
      (iDs,ivi,iiv,ivv) = IM.findWithDefault infoR0 fID irM
      fact0' = SInfo (IM.insert fEntryId ivi mempty)(IM.insert fEntryId iiv mempty)
             (IM.insert fEntryId ivv mempty)(IM.insert fEntryId iDs mempty)
             (IM.insert fEntryId (fVars S.\\ iDs) mempty)            
      fact0 = (varVarMap %~ IM.insert fEntryId fVV0) $! 
              (preVarMap %~ IM.insert fEntryId fVars) top 
      analysis = fwdDataflowAnalysis top meetSliceInfo sliceTransfer  
--      fwdIRs = IM.filterWithKey (\k _ -> k < 0) irM
--  analysisPut (SState 0 fwdIRs)   -- setFwdInfoR fwdIRs
  localInfo <- analysisLocal envMod (dataflow funcLike analysis fact0)  -- fact0'
  SState tr irM2 <- analysisGet 
  let trStr = fName ++ fStrLn ++ "\'s #Insts_traced = " ++ show tr -- (length tr)
      fStrLn = case getFunctionLine f of
               Just (src, ln) -> "(Defined at " ++ src ++ ":" ++ show ln ++ ")"
               Nothing        -> ""
      si@(SInfo viM ivM vvM dsM _) = dataflowResult localInfo 
      !fR@(fDs,fVIs,fIVs,fVVs) = findInfoRels si fExitIds
      iRs = (-fID,fR):(zip fBBExitIds $ map (findInfoRel si) fBBExitIds)
      irM' = addInfoRels irM2 iRs
      fSummEdge = R.mkRel $ concatMap getSummEdge fFmls
--             `debug` (show fIVs)     -- computeSummEdge si f 
        where toAlias ai = maybeToList $ M.lookup ai fAliasMap
              getSummEdge ai = [(ai,bi) | bi <- argNodes]   
               where !ais = toAlias ai    
                     ais' = ai:ais                
                     argNodes = intersect fFmls ais'                            
                     bwdSli v = R.domOf v fIVs 
--                     fVVs' =  findIMWith ((-fID):fInstIds) vvM                         
  return $ (traceSize %~ (+) tr)  
         $ (funSummEdges %~ IM.insert fID fSummEdge)
         $! (funInfoRel %~ IM.unionWith mrgInfoRel irM') s  
--             `debug` (show $ IM.keys irM')    -- (trStr ++ "\n" ++ show irM2)   
  where
    f = getFunction funcLike  
    fID = functionUniqueId f              
    fName = identifierAsString (functionName f)
    fEntryId = instructionUniqueId $ functionEntryInstruction f
    fExitIds = map valueUniqueId $ functionExitInstructions f
    fBBExitIds = map (valueUniqueId. basicBlockTerminatorInstruction) (functionBody f)
--    fInstIds = map valueUniqueId $ functionInstructions f
    fAliasMap = M.fromList $ getFunAlias f
    fFmls = varFilter (glbVars ++ fmlVars) 
    fVV0 = R.idR fVars
    fVars = S.fromList allVars
    --
    glbVars = map toVarName' $ moduleGlobalVariables m
    fmlVars = map toVarName' $ functionParameters f 
    locVars = map toVarName' $ funcAllocInsts f
    allVars = varFilter $ glbVars ++ fmlVars ++ locVars
    varFilter = filter ((/="."). drop 1. take 2) 


type IsParallel = Bool
computeSlice :: IsParallel -> Module -> SliceSummary
computeSlice isPar m = _sliceSumm res    -- `showGraph` (cg,mName,"CallGraph")
  where
    cg = callGraph m pta [] 
    pta = runPointsToAnalysis m
--    mName = T.unpack $ moduleIdentifier m
    analyses :: [ComposableAnalysis SliceAnalysis Function]
    analyses = [ identifySlice m cg sliceSumm ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = cgTraversal cg analysisFunc mempty    
    cgTraversal = if isPar then parallelCallGraphSCCTraversal else callGraphSCCTraversal 

---------------
genSliceTable2 :: IsParallel -> Module -> (Map String [String],Map String [String])
genSliceTable2 isPar m = (toSrcLns bwdST, toSrcLns fwdST)
  where (bwdST,fwdST) = genSliceTable isPar m
        valMap = genValueMap m
        toSrcLns = M.map (toSrcLnStr valMap) 

genSliceTable :: IsParallel -> Module -> (SliceTable,SliceTable)    
genSliceTable isPar m = getSliceTable summary valMap m
  where !summary = computeSlice isPar m
        valMap = genValueMap m    
        
getSliceTable :: SliceSummary -> IntMap Value -> Module -> (SliceTable,SliceTable)    
getSliceTable summary valMap m = (bwdSlices, fwdSlices)   `debug` (showVVs vvs) 
  where infoRelM = _funInfoRel summary
        (_,vis,ivs,vvs) = mrgInfoRels . IM.elems $ IM.filterWithKey (\k _ -> k < 0) infoRelM
        fwdSliTbl = relToFwdSliTbl vis
        bwdSliTbl = relToBwdSliTbl ivs   
        bwdSlices = reduceKey $ addAlias aliasMap bwdSliTbl
        fwdSlices = reduceKey $ addAlias aliasMap fwdSliTbl  
        aliasMap = genAliasMap m      
        reduceKey = M.mapKeys (drop 1). M.filterWithKey (\(_:k:_) _->(isLetter k || k == '_'))
        --
        showVVs = showMapWith "\n Variable   --->    Variables  " id . relToVVTbl
        trStr = "\n\tIts trace Info: #Insts_Symbolic = " ++ show (_traceSize summary)

addAlias :: Map String String -> SliceTable -> SliceTable
addAlias am s = updSlices aliNames aliSlices s 
  where  
    (aliNames,aliSlices) = unzip . concatMap fromAlias $ M.toList am
    fromAlias (v1,v2) = [(v1,unionSli),(v2,unionSli)] 
      where unionSli = IS.union (lkpSli v1 s) (lkpSli v2 s)


-----
relToFwdSliTbl :: R.Rel String Int -> SliceTable
relToFwdSliTbl = foldl' toSliT mempty . R.pairs
  where toSliT acc (v,i) = M.insertWith IS.union v (IS.singleton i) acc

relToBwdSliTbl :: R.Rel Int String -> SliceTable
relToBwdSliTbl = foldl' toSliT mempty . R.pairs
  where toSliT acc (i,v) = M.insertWith IS.union v (IS.singleton i) acc

relToVVTbl :: R.Rel String String -> Map String [String]
relToVVTbl = foldl' toTbl mempty . R.pairs
  where toTbl acc (v1,v2) = M.insertWith union v1 [v2] acc






 
