{-# LANGUAGE BangPatterns,ViewPatterns,DeriveGeneric,RankNTypes,TemplateHaskell #-}


module LLVM.Slicing.Static.Symbolic.SymSlicer (
 -- * Types
 SliceSummary(..),
 -- * Slice Computing
 computeSlice,
 genSliceTable, genSliceTable2
 )
 where

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
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS
import Data.Maybe 
import Data.Monoid 
import Data.List ( foldl' ) 
import Data.Char ( isLetter )
--import qualified Data.Text as T (unpack)

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
import LLVM.Slicing.Static.Symbolic.SymADT


------
data SliceSummary =
  SliceSummary {  _bwdSliceTable :: SliceTable
                , _procSliTblSumm :: IntMap SliceTable
                , _procInstDepSumm :: IntMap (IntMap IntSet)
                , _instDepSummary :: IntMap IntSet
--                , _fwdSliceTable :: SliceTable
                , _traceSize :: Int
                }
  deriving (Generic,Show)

$(makeLenses ''SliceSummary)

instance Eq SliceSummary where
  (SliceSummary bs1 ps1 pid1 _ _) == (SliceSummary bs2 ps2 pid2 _ _) =
    bs1 == bs2  && ps1 == ps2 && pid1 == pid2  

instance Monoid SliceSummary where
  mempty = SliceSummary mempty mempty mempty mempty 0 
  mappend (SliceSummary bs1 ps1 pid1 id1 tr1) (SliceSummary bs2 ps2 pid2 id2 tr2) =
    SliceSummary (mrgSli bs1 bs2)(IM.unionWith mrgSli ps1 ps2)
                 (IM.unionWith (IM.unionWith IS.union) pid1 pid2)
                 (IM.unionWith IS.union id1 id2)(tr1 + tr2)

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
-----
top :: SliceInfo
top = SInfo mempty mempty

meetSliceInfo :: SliceInfo -> SliceInfo -> SliceInfo
meetSliceInfo (SInfo !s1 !d1) (SInfo !s2 !d2) = 
          SInfo (mrgSli s1 s2) (IM.unionWith IS.union d1 d2)   

sliceTransfer :: SliceInfo -> Instruction -> Analysis SliceInfo
sliceTransfer si i =  do 
  cdM <- analysisEnvironment instCtrMap
  addTrace i
  case i of    
    StoreInst {storeAddress = ptr, storeValue = sv} -> 
      updSliInfo i (ptr,sv) si cdM
    AtomicRMWInst {atomicRMWPointer = ptr, atomicRMWValue = av} ->
      updSliInfo i (ptr,av) si cdM
    AtomicCmpXchgInst {atomicCmpXchgPointer = ptr, atomicCmpXchgNewValue = nv} ->
      updSliInfo i (ptr,nv) si cdM
      
    InsertValueInst {insertValueAggregate = a, insertValueValue = iv} -> 
      updSliInfo i (a,iv) si cdM
----    PhiNode {} -> updSliInfo i (toValue i, toValue i) si cdM
      
    CallInst { callFunction = fv, callArguments = avs } ->
      callTransfer cdM si i fv (map fst avs)
    InvokeInst { invokeFunction = fv, invokeArguments = avs } ->
      callTransfer cdM si i fv (map fst avs)
      
    _ -> if isCtrInst i then setTrInstCtrDep cdM si i    
         else setTrInstDep cdM si i     
{-# INLINE sliceTransfer #-}

updSliInfo :: Instruction -> (Value,Value) -> SliceInfo -> IntMap ValueIds -> Analysis SliceInfo
updSliInfo i (ptr,v) si cdM
--  | instructionIsPhiNode i = addTrInstDep si' i l'
  | null (refs ptr) = addTrInstDep si i l'      
  | otherwise = case valueContent ptr of      
      InstructionC PhiNode {phiIncomingValues = (map fst -> ivs)} -> do
         let ptNames = mapMaybe toVarName (map memAccessBase ivs)  
             !si2 = if null ptNames then si 
                    else (sliceTable %~ xtdSli2 ptNames l') si    
         addTrInstDep si2 i l'
      InstructionC SelectInst {selectTrueValue = tv, selectFalseValue = fv} -> do
         let ptNames = mapMaybe toVarName (map memAccessBase [tv,fv])
             !si2 = if null ptNames then si 
                    else (sliceTable %~ xtdSli2 ptNames l') si    
         addTrInstDep si2 i l'
      _ -> addTrInstDep si' i l'
  where
    !l' = unionLs cdM si i v
    base = memAccessBase ptr
    baseName = toVarName base
    updOrXtdSli = if isAggregate ptr || isAggType base
                  then xtdSli else updSli
    !si' = if isNothing baseName then si
           else (sliceTable %~ updOrXtdSli (fromJust baseName) l') si


callTransfer :: IntMap ValueIds -> SliceInfo -> Instruction -> Value -> [Value] -> Analysis SliceInfo
callTransfer cdM si i fv cargs = do
  ptM <- analysisEnvironment procSliTbl
  pdM <- analysisEnvironment procInstDep
  paraMap <- analysisEnvironment paraValMap
  case valueContent' fv of
    FunctionC f -> do
      let fName = identifierAsString . functionName $ f  
          fID = functionUniqueId f
          procSli = IM.findWithDefault M.empty fID ptM 
          procIDep = IM.findWithDefault IM.empty fID pdM
          argMap = IM.filterWithKey mapF paraMap
             where mapF n (v,k) = k == -1 || elem n frmlIds
                   frmlIds = map valueUniqueId (functionParameters f)
          isArgIn v = lkpSli (toVarName' v) procSli == IS.singleton (- valueUniqueId v)
          noChgArgs = [toVarName' v | (v,k) <- IM.elems argMap, isArgIn v, k /= -1]
          noChgGlbs = [toVarName' v | (v,k) <- IM.elems argMap, isArgIn v, k == -1]
          iID = instructionUniqueId i
          iCtrDep = IS.insert iID $ findCD cdM si i      -- lkpCtrDep i si
          --
          procIDep' = IM.map fillF procIDep 
             where fillF !lx = IS.unions $ [lx1,iCtrDep] ++ lxs   
                     where (lx1,lx2) = IS.partition (>0) lx
                           lxs = map (lci. negate) $ IS.toList lx2     
                   lci n = case IM.lookup n argMap of                
                            Just (gv,-1) -> unionLs cdM si i gv
                            Just (v,k) -> unionLs cdM si i (cargs !! k)
                            _  -> IS.singleton (-n)
          !procSli' = M.mapWithKey fillF procSli 
             where fillF var !lx 
                     | elem var noChgGlbs = IS.empty
                     | elem var noChgArgs = iCtrDep
                     | otherwise  =  IS.unions $ [lx1,iCtrDep] ++ lxs   
                     where (lx1,lx2) = IS.partition (>0) lx
                           lxs = map (lci. negate) $ IS.toList lx2     
                   lci n = case IM.lookup n argMap of                
                            Just (gv,-1) -> unionLs cdM si i gv
                            Just (v,k) -> unionLs cdM si i (cargs !! k)
                            _  -> IS.singleton (-n)
          chgActArgs = [ (toVarName' (toActVar v k), lkpSli (toVarName' v) procSli') 
                        | (v,k) <- IM.elems argMap, not (isArgIn v)] 
             where toActVar v k = if k == -1 then v else memAccessBase (cargs !! k) 
          !si' = (sliceTable %~ updSlices argNames lxs. M.unionWithKey mapF procSli') si  
             where (argNames,lxs) = unzip chgActArgs
                   mapF k lx' lx = if (head k == '@') && not(IS.null lx') 
                                   then lx' else IS.union lx' lx
          si2 = if M.null procSli then si else si'
      setInstDep procIDep' 
      addTrInstDep si2 i iCtrDep       
    ExternalFunctionC ef      
      | isMemCMS ef   -> updSliInfo i (cargs!!0,cargs!!1) si cdM
      | isC99Scanf ef -> updSliInfo i (cargs!!1,cargs!!0) si cdM
      | isC99Read ef  -> updSliInfo i (cargs!!0,undef) si cdM
      | otherwise     -> setTrInstDep cdM si i 
      where  undef = ConstantC UndefValue {constantType=TypeVoid, constantUniqueId = 0}
    _ -> setTrInstDep cdM si i  


identifySlice ::    
       (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
        => Module -> Lens' compositeSummary SliceSummary
        -> ComposableAnalysis compositeSummary funcLike
identifySlice m lns =
  composableAnalysisM runner (sliceAnalysis m) lns
  where
    runner a = runAnalysis a constData cache
    constData = SEnv mempty mempty mempty mempty 
    cache = SState 0 mempty


sliceAnalysis :: (FuncLike funcLike, HasCFG funcLike,HasFunction funcLike)
               => Module -> funcLike -> SliceSummary -> Analysis SliceSummary
sliceAnalysis m funcLike s@(SliceSummary bs ptM pdM _ _) = do   
  let envMod e = e { procSliTbl = ptM
                   , procInstDep = pdM
                   , paraValMap = IM.fromList $ zip allParaIds allParaVals  
                   , instCtrMap = genCtrDepMap f  
                   }
      !fact0 = (sliceTable %~ xtdSlices fArgStrs fArgSlis) top
      analysis = fwdDataflowAnalysis top meetSliceInfo sliceTransfer  
  localInfo <- analysisLocal envMod (dataflow funcLike analysis fact0)   
  SState tr ideps <- analysisGet 
  let SInfo bs' _ = dataflowResult localInfo
--      !valMap = genValueMap m
--      fs' = getFwdSlices1 valMap ideps fs 
  return $ (procSliTblSumm %~ IM.insertWith' mrgSli fID bs')      
         $ (procInstDepSumm %~ IM.insertWith' (IM.unionWith IS.union) fID ideps)      
         $ (instDepSummary %~ IM.unionWith IS.union ideps)           
--         $ (fwdSliceTable %~ mrgSli fs')
         $ (traceSize %~ (+) tr)
         $! (bwdSliceTable %~ mrgSli bs') s   
  where
    f = getFunction funcLike 
    fID = functionUniqueId f 
    (fArgStrs,fArgSlis) = unzip $ map initSlice fParaVals
      where initSlice (v,n) 
              | n == -2   =  (toVarName' v, IS.empty) 
              | otherwise =  (toVarName' v, IS.singleton $ - valueUniqueId v) 
    fParaIds = map (valueUniqueId . fst) fParaVals        
    fParaVals = frmlVals f ++ globalVals ++ allocVals f
    --
    allParaIds = map (valueUniqueId . fst) allParaVals
    allParaVals = globalVals ++ (concatMap frmlVals $ moduleDefinedFunctions m)
    frmlVals fn = zip (map toValue $ functionParameters fn) [0..]
    globalVals = zip (map toValue $ moduleGlobalVariables m) (repeat (-1))
    allocVals fn = zip (map toValue $ funcAllocInsts fn) (repeat (-2))

----
type IsParallel = Bool
computeSlice :: IsParallel -> Module -> SliceSummary
computeSlice isPar m = _sliceSumm res    -- `showGraph` (cg,mName)
  where
    cg = callGraph m ics []
    ics = runPointsToAnalysis m
--    mName = T.unpack $ moduleIdentifier m
    analyses :: [ComposableAnalysis SliceAnalysis Function]
    analyses = [ identifySlice m sliceSumm ]
    analysisFunc = callGraphComposeAnalysis analyses   
    res = cgTraversal cg analysisFunc mempty      
    cgTraversal = if isPar then parallelCallGraphSCCTraversal else callGraphSCCTraversal

-------------
genSliceTable2 :: IsParallel -> Module -> (Map String [String],Map String [String])
genSliceTable2 isPar m = (toSrcLns bwdST, toSrcLns fwdST)
  where (bwdST,fwdST) = genSliceTable isPar m
        valMap = genValueMap m
        toSrcLns = M.map (toSrcLnStr valMap) 

genSliceTable :: IsParallel -> Module -> (SliceTable,SliceTable)    
genSliceTable isPar m = (bwdSlices, fwdSlices) 
  where !summary = computeSlice isPar m
        aliasMap = genAliasMap m
        valMap = genValueMap m
        bwdSlices = reduceKey. addAlias aliasMap $ _bwdSliceTable summary
        fwdSlices = reduceKey. addAlias aliasMap. getFwdSlices valMap $ _instDepSummary summary
        reduceKey = M.mapKeys (drop 1). M.filterWithKey (\(_:k:_) _->(isLetter k || k == '_'))
     
addAlias :: Map String String -> SliceTable -> SliceTable
addAlias am s = updSlices aliNames aliSlices s
  where  
    (aliNames,aliSlices) = unzip . concatMap fromAlias $ M.toList am
    fromAlias (v1,v2) = [(v1,unionSli),(v2,unionSli)] 
      where unionSli = IS.union (lkpSli v1 s) (lkpSli v2 s)


--------------
---
        
getFwdSlices :: IntMap Value -> IntMap ValueIds -> SliceTable
getFwdSlices valMap idepMap =  M.mapWithKey mapF fwdSlices'
  where 
    fwdSlices' = IM.foldlWithKey' doInvert mempty idepMap
    doInvert !acc i !ls = 
      foldl' (\a v -> M.insertWith' IS.union v (IS.singleton i) a) acc (toVars ls)    
    toVars = concatMap refs . findVals valMap 
    mapF k !ls = foldl' (instLine k) IS.empty $ findVals valMap ls
    instLine k !ls i = case valueContent' i of 
       InstructionC RetInst {retInstValue = Nothing } -> ls
       InstructionC RetInst {retInstValue = Just (valueContent -> ConstantC{})} -> ls
       InstructionC UnconditionalBranchInst { } -> ls 
       InstructionC UnreachableInst { } -> ls
       InstructionC FenceInst { } -> ls
       _    ->  IS.insert (valueUniqueId i) ls 
{-# INLINE getFwdSlices #-}





    

     


      


    


