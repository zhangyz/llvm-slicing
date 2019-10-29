{-# LANGUAGE BangPatterns,DeriveGeneric,NoMonomorphismRestriction,TemplateHaskell,FlexibleContexts  #-}
 

module LLVM.Slicing.Static.InfoFlow.InfoFlowADT where

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
import Data.Set ( Set )
import qualified Data.Set as S
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS
import Data.Maybe  
import Data.Monoid ( mempty )
import Data.List  
import Text.Printf ( printf )  
import Data.Char ( isDigit )
import qualified Data.Relation as R

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraph

import LLVM.Slicing.Util.Utils
import LLVM.Slicing.Data.SliceType 


--import Debug.Trace ( trace )

---------------
maxNumID = maxBound :: Int 
getNewId i n = div maxNumID (n + 1) - i
toDefVars fms = mapMaybe toVarName. HS.toList . valueDefs fms
toDefVars2 = mapMaybe toVarName. HS.toList . directValueDefs    -- defs
toRefVar = map toVarName' . HS.toList . refVals
toRefVars2 v = mapMaybe toVarName $ v : directValueRefs v      -- refs
isGlbVar2 v = (head $ toVarName' v) == '@' 
isGlbVar s = head s == '@'

type InfoFlowRel = (Set String, R.Rel String Int, R.Rel Int String, R.Rel String String)

data SliceEnv = SEnv { fCFG :: CFG
                     , callGr :: CallGraph
                     , summEdges :: IntMap (R.Rel String String)
                     , fInfoRels :: IntMap InfoFlowRel
                     , fAllVars :: Set String}                      

data SliceState = SState { traces :: !Int 
                         , fwdInfoRs :: IntMap InfoFlowRel
                         } deriving (Generic)


data SliceInfo = SInfo { _varInstMap :: IntMap (R.Rel String Int)    -- 
                       , _instVarMap :: IntMap (R.Rel Int String)                        
                       , _varVarMap :: IntMap (R.Rel String String) 
                       , _defVarMap :: IntMap (Set String)
                       , _preVarMap :: IntMap (Set String) 
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

getFwdInfoR :: Analysis (IntMap InfoFlowRel) 
getFwdInfoR = do {s <- analysisGet; return (fwdInfoRs s) }  

addFwdInfoR :: Int -> InfoFlowRel -> Analysis ()
addFwdInfoR fID ir = do 
  SState tr irM <- analysisGet  
  let !irM' = IM.insertWith mrgInfoRel fID ir irM   
  analysisPut (SState tr irM')  

setFwdInfoR :: IntMap InfoFlowRel -> Analysis ()
setFwdInfoR irM' = do 
  s <- analysisGet 
  analysisPut s { fwdInfoRs = irM'} 
------------------------------------------------------ 
lkpDs ::  SliceInfo -> Instruction -> Set String 
lkpDs si i = 
   IM.findWithDefault S.empty (instructionUniqueId i) $! si ^. defVarMap
{-# INLINE lkpDs #-}

lkpPs ::  SliceInfo -> Instruction -> Set String 
lkpPs si i = 
   IM.findWithDefault S.empty (instructionUniqueId i) $! si ^. preVarMap
{-# INLINE lkpPs #-}

lkpVI ::  SliceInfo -> Instruction -> R.Rel String Int
lkpVI si i = 
   IM.findWithDefault S.empty (instructionUniqueId i) $! si ^. varInstMap
{-# INLINE lkpVI #-}

lkpIV ::  SliceInfo -> Instruction -> R.Rel Int String 
lkpIV si i = 
   IM.findWithDefault S.empty (instructionUniqueId i) $! si ^. instVarMap
{-# INLINE lkpIV #-}

lkpVV ::  SliceInfo -> Instruction -> R.Rel String String 
lkpVV si i = 
   IM.findWithDefault S.empty (instructionUniqueId i) $! si ^. varVarMap
{-# INLINE lkpVV #-}

findIMWith :: (Ord a) => [Int] -> IntMap (Set a) -> Set a
findIMWith ks = S.unions . IM.elems . IM.filterWithKey keyF 
   where keyF k _ = elem k ks 
{-# INLINE findIMWith #-}

------
mrgInfoRel :: InfoFlowRel -> InfoFlowRel -> InfoFlowRel
mrgInfoRel (iDs1,ivi1,iiv1,ivv1) (iDs2,ivi2,iiv2,ivv2) =
  (S.union iDs1 iDs2,S.union ivi1 ivi2,S.union iiv1 iiv2,S.union ivv1 ivv2)  
  
mrgInfoRels :: [InfoFlowRel] -> InfoFlowRel  
mrgInfoRels  = foldl' mrgInfoRel mempty 

findInfoRel :: SliceInfo -> Int -> InfoFlowRel
findInfoRel si@(SInfo viM ivM vvM dM pM) k  = 
 (IM.findWithDefault S.empty k dM, IM.findWithDefault S.empty k viM,
  IM.findWithDefault S.empty k ivM,IM.findWithDefault S.empty k vvM )

findInfoRels :: SliceInfo -> [Int] -> InfoFlowRel
findInfoRels si@(SInfo viM ivM vvM dM pM) ks  = 
 (findIMWith ks dM,findIMWith ks viM,findIMWith ks ivM,findIMWith ks vvM)

addInfoRel :: IntMap InfoFlowRel -> (Int,InfoFlowRel) -> IntMap InfoFlowRel
addInfoRel irM (k,ir) = IM.insertWith mrgInfoRel k ir irM 

addInfoRels :: IntMap InfoFlowRel -> [(Int,InfoFlowRel)] -> IntMap InfoFlowRel  
addInfoRels irM = foldl' addInfoRel irM

lkpInfoRels :: [Int] -> IntMap InfoFlowRel -> InfoFlowRel
lkpInfoRels ks = mrgInfoRels . IM.elems . IM.filterWithKey keyF
   where keyF k _ = elem k ks 
------------------
----
getInfoRel :: Value -> [String] -> Set String -> InfoFlowRel
getInfoRel sv ds vs = (iDs,ivi,iiv,ivv)  
  where  ivi = if null svRefs then R.emptyR 
               else R.mkRel [(v,svID)| v <- svRefs ]
         iiv = if null ds then R.emptyR
               else R.mkRel [(n,v) | n <- svRefIDs, v <- ds] 
         ivv0 = if null svRefs || null ds then R.emptyR 
                else R.mkRel [(v1,v2) | v1 <- svRefs, v2 <- ds] 
         ivv = S.union ivv0 . R.idR $ vs S.\\ iDs
         iDs = S.fromList ds
         svID = valueUniqueId sv  -- (memAccessBase sv)
         svRefIDs = map valueUniqueId $ sv : (HS.toList $ valueRefs sv) -- (directValueRefs sv)
         svRefs = if isExtFunction sv then [] else refs sv         -- toRefVar
{-# INLINE getInfoRel #-}

updateInfoRel :: SliceInfo -> Instruction -> InfoFlowRel -> Analysis SliceInfo
updateInfoRel si@(SInfo viM ivM vvM dM pM) i (iDs,ivi,iiv,ivv) = do   
   cfg <- analysisEnvironment fCFG
   let  iID = instructionUniqueId i 
        iPreds = if isFunEntryInst i then [iID]
                 else map valueUniqueId $ instructionPredecessors cfg i
        iPreds2 = if isBBEntryInst i then [iID]
                  else map valueUniqueId $ instructionPredecessors cfg i
        (_,ivi0,iiv0,ivv0) = findInfoRels si iPreds 
        iDs0 = findIMWith iPreds2 dM
        iPs0 = findIMWith iPreds pM
        iPs' = iPs0 S.\\ (S.intersection iDs iPs0)
        iDs' = S.union iDs0 iDs    
        ivi' = S.union ivi0 $ (R..~) ivi ivv0    -- ivi 
        iiv' = S.union iiv $ (R..~) ivv iiv0
        ivv' = (R..~) ivv ivv0       
        !si' = (defVarMap %~ IM.insertWith S.union iID iDs')
                $! (preVarMap %~ IM.insertWith S.union iID iPs') si
        !si2 = (varInstMap %~ IM.insertWith S.union iID ivi')
              $ (instVarMap %~ IM.insertWith S.union iID iiv')
              $! (varVarMap %~ IM.insertWith S.union iID ivv') si'
        dbgStr = printf ("(%s) \"%s\": \n  iVI_A = %s \n  iVI_B = %s \n  iVI_AB = %s \n")
             (show $ valueUniqueId i) (show i) (show ivi0)(show ivi)(show ivi')
   return $! si2   --  `debug`  dbgStr    
{-# INLINE updateInfoRel #-}

computeInfoRel :: SliceInfo -> Instruction -> Analysis SliceInfo
computeInfoRel si i = do
  fVars <- analysisEnvironment fAllVars
  let iv = toValue i
      iDefs = toDefVars2 i     -- toDefVars fms i  
      !infoR = getInfoRel iv iDefs fVars
  updateInfoRel si i infoR  
{-# INLINE computeInfoRel #-}


doCallInfo :: SliceInfo -> Instruction -> Value -> [Value] -> Analysis SliceInfo 
doCallInfo si@(SInfo viM ivM vvM dM pM) i fv cargs = do
  SEnv cfg cg summMap infoRMap fVars <- RW.ask 
  let iID = valueUniqueId i
      iDefs = toDefVars2 i     -- toDefVars fms i
      iRefs = refs i         -- toRefVar  
      glbVars = S.filter isGlbVar fVars 
      glbVVs = R.idR glbVars
      iPreCtrInsts = map basicBlockTerminatorInstruction ps
        where  Just bb = instructionBasicBlock i
               ps = basicBlockPredecessors cfg bb
      instMap = case instructionFunction i of 
          Just f  -> let is = functionInstructions f 
                     in IM.fromList $ zip (map valueUniqueId is) is 
          Nothing -> IM.empty
      findInstMap ks = IM.elems $ IM.filterWithKey (\k _ -> S.member k ks) instMap
  case valueContent' fv of
   FunctionC f -> do
     let fID = functionUniqueId f 
         fSumms = IM.findWithDefault R.emptyR fID summMap
         fCallFs = mapMaybe getFunc $ allFunctionCallees cg f
         fCallVs = nub $ concatMap functionVars fCallFs
         fCallIDs = map (negate . functionUniqueId) fCallFs
         fEntryId = valueUniqueId $ functionEntryInstruction f
         funcLocs = filter (\(_:k:_) -> (not $ isDigit k)). map toVarName'. funcAllocInsts 
         fLocs = map toVarName' $ funcAllocInsts f
         cargs' = map memAccessBase cargs
         fargs = functionParameters f
         fFmls = map toVarName' fargs
         fActs = map toVarName' cargs'
         fVs = fFmls ++ fLocs ++ S.elems glbVars
         fFmlAct = zip fFmls fActs ++ S.elems glbVVs
         fActFml = [(toVarName' v,toVarName' a) |(v,a) <- zip cargs' fargs
                     , not (isConstantValue v)] ++ S.elems glbVVs         -- isValidVar
         argMap = M.fromList fFmlAct  
         argMap' = M.filterWithKey (\k _ -> S.member k $ R.dom fSumms) argMap 
--         fFmlAct' = filter (flip S.member (R.dom fSumms)) fFmlAct
         fSumms' = [(toAct a,toAct b)| (a,b) <- S.elems fSumms]
           where toAct fml = M.findWithDefault "*UNKNOWN*" fml argMap
--         vSumm v = [ b | (a,b) <- fSumms', a == v ] 
         fAliaFml = R.inv . R.mkRel $ getFunAlias f
     let 
         iPreds = if isFunEntryInst i then [iID] 
                  else map valueUniqueId $ instructionPredecessors cfg i
         iPreds2 = if isBBEntryInst i then [iID]
                  else map valueUniqueId $ instructionPredecessors cfg i
         (_,ivi0,iiv0,ivv0) = findInfoRels si iPreds 
         iDs0 = findIMWith iPreds2 dM
         iPs0 = findIMWith iPreds pM 
         (_,fVI0,fIV0,fVV0) = IM.findWithDefault mempty (-fID) infoRMap                   
         (_,allVI0,allIV0,allVV0) = mrgInfoRels $ IM.elems fRs
            where fRs = IM.filterWithKey (\k _ -> elem k fCallIDs) infoRMap
         funcVVs = S.union actFmlVV $ (R..~) fVV0 actFmlVV    -- allVV0
         actFmlVV = R.mkRel fActFml  
         fmlActVV = S.union fmlActVV' $ (R..~) fmlActVV' fAliaFml
         fmlActVV' = R.mkRel $ M.toList argMap'
         (actOutVar,actInVar) = ((nub $ map fst fSumms'), nub $ map snd fSumms')
         --
         findII n = flip (R..~) iiv0 $ S.filter ((== n). snd) ivi0
         findIIs ns = flip (R..~) iiv0 $ S.filter (flip S.member ns. snd) ivi0
         findCDInsts = filter isCtrInst. findInstMap . R.dom . findII
         getInstDep i = R.dom $ S.filter (flip elem (refs i). snd) iiv0
         getCallDep n = S.toList . S.unions $ iCD : iDDs 
            where iCD  = S.fromList $ map valueUniqueId iCD'
                  iDDs = map getInstDep iCD'
                  iCD' = findCDInsts n
     let 
         fVIs2 = (R..~) vis ivvs 
            where vis = S.union fVI0 allVI0  
                  ivvs = S.union funcVVs $ (R..~) funcVVs ivv0
         fIVs2 = S.unions [iiv1,iiv2,iiv3]   -- `debug` (show $ getCallDep iID) 
            where iiv1 = mkRelNeighbors iID locVars     
                  iiv1' = mkRelNeighbors iID actInVar
                  iiv2 = (R..~) ivvs $ S.union iiv1' iiv0  
                  ivvs = (R..~) (S.union fVV0 allVV0) funcVVs
                  iiv3 = R.mkRel [(i,v)| i <- getCallDep iID, v <- locVars ++ fFmls ]
                  !locVars = concatMap funcLocs $ f:fCallFs  
         fVVs2 =  funcVVs
            where  ivvs = S.union funcVVs $ (R..~) funcVVs ivv0
     addFwdInfoR (-fID) (mempty, fVIs2, fIVs2, fVVs2) 
     let 
         iDs = S.fromList actOutVar 
         iDs2 = S.unions [iDs,iDs0,S.fromList fFmls]
         iPs = iPs0 S.\\ (S.intersection iDs iPs0)    -- fVars S.\\ iDs
         ivi = S.unions [ivi0,ivi1,ivi2,ivi2']  -- [ivi0,ivi2']
            where ivi1 = R.mkRel [(v,iID)| v <- actInVar ]   
                  ivi1' = R.mkRel [(v,iID)| v <- actOutVar ]
                  ivi2 = (R..~) ivi1 ivv0
                  ivi2' = (R..~) ivi1' vvs 
                  vvs = (R..~) fmlActVV fVV0   -- S.union fmlActVV $ 
         iiv = S.unions [iiv1,iiv2,iiv3]   -- [iiv1,fmlIVs]   
            where iiv1 = mkRelNeighbors iID actOutVar 
                  iiv2 = (R..~) ivv' iiv0    
                  fmlIVs = (R..~) fmlActVV fIV0   
                  iiv3 = (R..~) ivv' fmlIVs
         ivv = S.unions [ivv1,ivv2]     -- `debug` (show fmlActVV)
            where ivv1 = (R..~) ivv' $ (R..~) fmlActVV fVV0
                  ivv2 = (R..~) ivv' ivv0    
         ivv' = S.unions [ivv1,ivv2]    
            where ivv1 = R.idR $ fVars S.\\ iDs  
                  ivv2 = R.mkRel $ [(v1,v2) | (v2,v1) <- fSumms']
         !si' = (defVarMap %~ IM.insertWith S.union iID iDs2)
              $! (preVarMap %~ IM.insertWith S.union iID iPs) 
              $ (varInstMap %~ IM.insertWith S.union iID ivi)
              $ (instVarMap %~ IM.insertWith S.union iID iiv)
              $! (varVarMap %~ IM.insertWith S.union iID ivv) si  
     return $! si'    --  `debug` (show (valueUniqueId i) ++ ": " ++ show (_defVarMap si')) 
         -- (varInstMap %~ IM.insertWith S.union iID ivi) 
--     let          
--         ivi2 = S.unions [ivi1',ivi1]  -- [ivi0,ivi2']
--            where ivi1 = R.mkRel [(v,iID)| v <- actInVar ]   
--                  ivi1' = R.mkRel [(v,iID)| v <- actOutVar ]
--                  ivi2 = (R..~) ivi1 ivv0
--                  ivi2' = (R..~) ivi1' vvs 
--                  vvs = (R..~) fmlActVV fVV0   -- S.union fmlActVV $ 
--         iiv2 = S.unions [iiv1]   
--            where iiv1 = mkRelNeighbors iID actOutVar 
--                  iiv2 = (R..~) ivv' iiv0    
--                  fmlIVs = (R..~) fmlActVV fIV0   
--                  iiv3 = (R..~) ivv' fmlIVs
--         ivv2 = S.unions [ivv1,ivv2]     -- `debug` (show fmlActVV)
--            where ivv1 = (R..~) ivv' $ (R..~) fmlActVV fVV0
--                  ivv2 = (R..~) ivv' ivv0  
--     updateInfoRel si i (iDs,ivi2,iiv2,ivv')  -- `debug` (show ivi)
   _ -> computeInfoRel si i
       -- updateInfoRel si i $ getInfoRel (toValue i) [] fVars      
{-# INLINE doCallInfo #-} 

doBrInfo :: SliceInfo -> Instruction -> [BasicBlock] -> Analysis SliceInfo
doBrInfo si@(SInfo viM ivM vvM dsM _) i blks = do
  fVars <- analysisEnvironment fAllVars
  irM <- analysisEnvironment fInfoRels
  let bIs = map (valueUniqueId. basicBlockTerminatorInstruction) blks 
      !infoR0@(iDs,_,_,_) = lkpInfoRels bIs irM 
--      !iDs = findIMWith bIs dsM    
--      !infoR0 = (iDs,findIMWith bIs viM,findIMWith bIs ivM,findIMWith bIs vvM) 
      !infoR@(iDs',_,iiv',_) = getInfoRel (toValue i) (S.elems iDs) fVars   
      infoR' = mrgInfoRel infoR0 infoR
  updateInfoRel si i infoR   --  `debug` (show (valueUniqueId i) ++ ": " ++ show iiv')
{-# INLINE doBrInfo #-}

doUnBrInfo :: SliceInfo -> Instruction -> Instruction -> Analysis SliceInfo
doUnBrInfo si i bi = do
  fVars <- analysisEnvironment fAllVars
  let ivi = (R..~) ivi0 ivv'
      iiv = S.union iiv' $ (R..~) (R.idR fVars) ((R..~) ivv' iiv0)
      ivv = (R..~) (R.idR fVars) ivv' 
      iDs = lkpDs si bi   
      iiv' = R.mkRel [(iID,v)| v <- S.elems iDs]
      ivv' = R.inv ivv0
      (ivi0,iiv0,ivv0) = (lkpVI si bi,lkpIV si bi,lkpVV si bi)
      iID = valueUniqueId i
  updateInfoRel si i (iDs,ivi,iiv,ivv)   --  `debug` (show iiv)
{-# INLINE doUnBrInfo #-}


--------------------------------------------------------------
------
computeInfoRel' :: SliceInfo -> Instruction -> Analysis SliceInfo
computeInfoRel' si@(SInfo viM ivM vvM dM pM) i = do
  fVars <- analysisEnvironment fAllVars
  cfg <- analysisEnvironment fCFG
  let iID = valueUniqueId i
      iDefs = toDefVars2 i    --  toDefVars fms i
      iRefs = refs i         -- toRefVar      
      iPreds = if isFunEntryInst i then [iID]
               else map valueUniqueId $ instructionPredecessors cfg i
      lkpA's = findIMWith iPreds
      (iviA,iivA,ivvA,iDsA,iPsA) = 
           (lkpA's viM, lkpA's ivM, lkpA's vvM, lkpA's dM, lkpA's pM)
  let iviB = if null iRefs then R.emptyR 
             else R.mkRel [(v,iID)| v <- iRefs ]
      iivB = if null iDefs then R.emptyR
             else mkRelNeighbors iID iDefs 
      ivvB = S.union ivv0 $ R.idR iPsB 
      ivv0 = if null iRefs || null iDefs then R.emptyR 
             else R.mkRel [(v1,v2) | v1 <- iRefs, v2 <- iDefs]
      iDsB = S.fromList iDefs
      iPsB = fVars S.\\ iDsB
  let iviAB = S.union iviA $ (R..~) iviB ivvA    -- ivi 
      iivAB = S.union iivB $ (R..~) ivvB iivA
      ivvAB = (R..~) ivvB ivvA 
      iDsAB = S.union iDsA iDsB
      iPsAB = S.intersection iPsA iPsB
  let !viM' = IM.insertWith S.union iID iviAB viM
      !ivM' = IM.insertWith S.union iID iivAB ivM
      !vvM' = IM.insertWith S.union iID ivvAB vvM 
      !dM' = IM.insertWith S.union iID iDsAB dM
      !pM' = IM.insertWith S.union iID iPsAB pM
  return $! (SInfo viM' ivM' vvM' dM' pM') 

getInfoRel' :: Value -> [String] -> Set String -> InfoFlowRel
getInfoRel' sv ds vs = (iDs,ivi,iiv,ivv)
  where  ivi = if null svRefs then R.emptyR 
               else R.mkRel [(v,svID)| v <- svRefs ]
         iiv = if null ds then R.emptyR
               else mkRelNeighbors svID ds
         ivv0 = if null svRefs || null ds then R.emptyR 
               else R.mkRel [(v1,v2) | v1 <- svRefs, v2 <- ds] 
         ivv = S.union ivv0 . R.idR $ vs S.\\ iDs
         iDs = S.fromList ds
         svID = valueUniqueId (memAccessBase sv)
         svRefs = refs sv         -- toRefVar
{-# INLINE getInfoRel' #-}

getUnBrIR :: SliceInfo -> Instruction -> Set String -> InfoFlowRel
getUnBrIR si bi vs = (iDs,ivi,iiv,ivv)
  where  ivi = S.union ivi0 $ (R..~) ivi0 ivv'
         iiv = S.union iiv0 $ (R..~) (R.idR vs) ((R..~) ivv' iiv0)
         ivv = S.union ivv0 $ (R..~) (R.idR vs) ivv' 
         iDs = lkpDs si bi
         ivv' = R.inv ivv0
         (ivi0,iiv0,ivv0) = (lkpVI si bi,lkpIV si bi, lkpVV si bi)
{-# INLINE getUnBrIR #-}

getBrIR :: SliceInfo -> Value -> [Int] -> Set String -> InfoFlowRel
getBrIR si@(SInfo viM ivM vvM dsM _) sv bIs vs = (iDs,ivi,iiv,ivv)
  where  (ivi,iiv,ivv) = (S.union ivi' ivi0, S.union iiv' iiv0,
                          S.union ivv' ivv0)
         ivi' = if null svRefs then R.emptyR 
                else R.mkRel [(v,svID)| v <- svRefs, svID <- svIDs ]
         iiv' = if null ds then R.emptyR
                else R.mkRel [(svID,v)| v <- ds, svID <- svIDs ] 
         ivv' = S.union ivv2 . R.idR $ vs S.\\ iDs
         ivv2 = if null svRefs || null ds then R.emptyR 
                else R.mkRel [(v1,v2) | v1 <- svRefs, v2 <- ds] 
         (iDs,ivi0,iiv0,ivv0) = ((findIMWith bIs dsM), (findIMWith bIs viM),
                                 (findIMWith bIs ivM), (findIMWith bIs vvM))
         ds = S.elems iDs
         svIDs = map valueUniqueId (HS.toList $ refVals sv)
         svRefs = refs sv         -- toRefVar      
{-# INLINE getBrIR #-}

getCallIR :: Instruction -> Value -> [Value] -> IntMap (R.Rel String String)
             -> IntMap InfoFlowRel -> Set String -> InfoFlowRel
getCallIR i fv cargs sm irm vs = 
  case valueContent' fv of
   FunctionC f -> (iDs,ivi,iiv,ivv)   -- `debug` (show fSumms)
     where iID = instructionUniqueId i
           fID = functionUniqueId f 
           (_,fVIs,fIVs,_) = IM.findWithDefault mempty fID irm
           fFmls = map toVarName' $ functionParameters f
           fActs = map toVarName' cargs
           argMap = M.fromList $ zip fFmls fActs
           toAct fml = M.findWithDefault "" fml
           fSumms = IM.findWithDefault R.emptyR fID sm
           fSumms' = [(toAct a argMap,toAct b argMap)| (a,b) <- S.elems fSumms] 
           argMap' = M.filterWithKey (\k _ -> S.member k $ R.dom fSumms) argMap 
           vSumm v = [ b | (a,b) <- fSumms', a == v ]
           fmlActVV = M.toList argMap'
           actIVs = (R..~) (R.mkRel fmlActVV) fIVs
           actOutVar = map snd fmlActVV
           actFmlVV = zip fActs fFmls 
           actVIs = (R..~) fVIs (R.mkRel actFmlVV) 
           iDs = S.fromList actOutVar  
           ivi = S.union actVIs $ R.mkRel [(v,iID)| v <- nub $ concatMap vSumm actOutVar]
           iiv = S.union actIVs $ R.mkRel [(iID,v)| v <- actOutVar] 
           ivv0 = R.mkRel $ [(v1,v2) | v2 <- actOutVar, v1 <- vSumm v2] ++ actFmlVV ++ fmlActVV
           ivv = S.union ivv0 . R.idR $ vs S.\\ iDs
   ExternalFunctionC ef -> getInfoRel (toValue i) (toDefVars2 i) vs          
{-# INLINE getCallIR #-}      

computeSummEdge :: SliceInfo -> Function -> R.Rel String String
computeSummEdge si f = R.mkRel $ concatMap getSummEdge fFmls
  where fID = functionUniqueId f 
        fFmls = mapMaybe (toVarName . toValue) $ functionParameters f    
        fExInsts = functionExitInstructions f
        fAliasMap = M.fromList $ getFunAlias f
        toAlias ai = maybeToList $ M.lookup ai fAliasMap
        fVVs = S.unions $ map (lkpVV si) fExInsts
        getSummEdge ai = [(ai,bi) | bi <- argNodes]
           where ais = ai : (toAlias ai)                
                 argNodes = intersect fFmls ais 
{-# INLINE computeSummEdge #-}    


-- 
mkRelNeighbors :: (Ord a, Ord b) => a -> [b] -> R.Rel a b
mkRelNeighbors a l  = R.mkRel [ (a, x) | x <- l ] 
