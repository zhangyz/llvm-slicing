{-# LANGUAGE BangPatterns,DeriveGeneric,NoMonomorphismRestriction,TemplateHaskell,FlexibleContexts  #-}
 

module LLVM.Slicing.Static.SDG.SDGADT where

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

import LLVM.Analysis
import LLVM.Analysis.CFG

import LLVM.Slicing.Util.Utils
import LLVM.Slicing.Data.SliceType 
import LLVM.Slicing.Static.SDG.SDGType

---------------
----
maxNumID = maxBound :: Int 
getNewId i n = div maxNumID (n + 1) - i

data SliceEnv = SEnv { fCFG :: CFG
                     , fModSet :: IntMap (HashSet Value)
                     , summEdges :: IntMap (Set ((Int,Int),Bool))
                     , paraValMap :: IntMap (Value,Int)
--                     , instCtrMap :: IntMap ValueIds 
                     }                      

data SliceState = SState { traces :: !Int  
                         , instCtrMap :: !(IntMap ValueIds)
                         } deriving (Generic)


data SliceInfo = SInfo { _nodeMap :: IntMap SDGNode
                       , _edgeMap :: Map (Int,Int) SDGEdge           
                       , _inMap :: IntMap (Set (Int,Int))
                       , _outMap :: IntMap (Set (Int,Int))
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
  

------------------------------------------------------ 

lkpIn ::  SliceInfo -> Instruction -> Set (Int,Int)
lkpIn si i = 
   IM.findWithDefault S.empty (instructionUniqueId i) $ si ^. inMap
{-# INLINE lkpIn #-}

lkpOut ::  SliceInfo -> Instruction -> Set (Int,Int)
lkpOut si i = 
   IM.findWithDefault S.empty (instructionUniqueId i) $ si ^. outMap
{-# INLINE lkpOut #-}

computeInOutWith :: Maybe (Value,[Value]) -> SliceInfo -> Instruction -> Analysis SliceInfo
computeInOutWith callInfo si i = do   
   fms <- analysisEnvironment fModSet
   cfg <- analysisEnvironment fCFG 
   paraMap <- analysisEnvironment paraValMap
   iInstCtr <- getInstCtr i
   let iDefIds = S.map valueUniqueId. S.fromList. HS.toList $ valueDefs fms i
       iRefIds = map valueUniqueId $ directValueRefs i -- instructionOperands i
--       iRefIds = HS.toList. HS.map valueUniqueId. HS.insert (toValue i) $ valueRefs i
       toRefIds v = map valueUniqueId $ v : directValueRefs v
       iRetIds = map valueUniqueId. filter ((/= valueFunction i). valueFunction). 
                 concatMap directValueRefs $ directValueRefs i
       iID = instructionUniqueId i 
       glbIds = IM.keys $ IM.filter ((== -1). snd) paraMap
       newId n = getNewId iID n  
       newId' n = -(getNewId iID n)
       iPreds = instructionPredecessors cfg i
       iCallInfo = do
           (fv,args) <- callInfo
           f <- getFunc fv
           let argVars = [(v,n) | (v,n) <- zip args [0..], not (isConstant v)]
           return (f,argVars)
       iGen =  S.map mapF iDefIds  
         where mapF d = fromMaybe (iID,d) $ do 
                   (f,argVars) <- iCallInfo
                   case find (isRef d) argVars of
                     Just (_,dn) -> if IM.member (newId' dn) (_nodeMap si)  
                                    then return (newId' dn,d)
                                    else find ((==d). snd) $ S.toList iIn
                     Nothing -> if not (elem d glbIds) then Nothing 
                                else return (newId' (d+10),d)
               isRef d (a,n) = elem d $ toRefIds a  
       iIn = S.unions $ map (lkpOut si) iPreds
       inKill = S.filter (not . flip S.member iDefIds . snd) iIn
       iOut = S.union inKill iGen   
       ---       
       (iDs,iVs) = unzip . S.toList $ S.filter (flip elem iRefIds. snd) iIn
       iDataDeps = nub $ iDs ++ (iRefIds \\ iVs) ++ (iRetIds \\ iRefIds)
       iDDEdges = M.fromList [((iID,d),DataDepEdge) | d <- iDataDeps]
       ddEdges = fromMaybe iDDEdges $ do 
           (f,argVars) <- iCallInfo              
           let ddEdges' = M.fromList (concatMap argDD argVars ++ concatMap glbDD glbIds)
               argDD (ai,an) = [((newId an, ad),DataDepEdge)| ad <- aiIn]
                 where aiIn = iDs ++ ([valueUniqueId ai] \\ iVs)
                       (iDs,iVs) = unzip . S.toList $ S.filter (flip elem aiRefs. snd) iIn 
                       aiRefs = toRefIds ai   
               glbDD g = [((newId (g+10), gd),DataDepEdge) | gd <- glbIn]
                 where glbIn = map fst. S.toList $ S.filter ((== g). snd) iIn
           return ddEdges'  
--       iInstCtr = IM.findWithDefault IS.empty (instructionUniqueId i) icm
       cdEdges = M.fromList [((b,iID),ControlDepEdge) | b <- IS.toList iInstCtr] 
       newEdges = if not (isCtrInst i) then ddEdges 
                  else M.union ddEdges cdEdges                 
   return $ (edgeMap %~ M.union newEdges)
          $ (inMap %~ IM.insertWith S.union iID iIn)
          $! (outMap %~ IM.insertWith S.union iID iOut) si 
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


addNodesEdgesAtCall :: Value -> [Value] -> SliceInfo -> Instruction -> Analysis SliceInfo
addNodesEdgesAtCall fv cargs si i = do
  se <- analysisEnvironment summEdges
  paraMap <- analysisEnvironment paraValMap
  let iID = instructionUniqueId i 
      newId n = getNewId iID n  
      newId' n = - newId n  
      glbIds = IM.keys $ IM.filter ((== -1). snd) paraMap 
      argVars = [(v,n) | (v,n) <- zip cargs [0..], not (isConstant v)]   
      actValIDs = mapFsts valueUniqueId argVars      
  case valueContent' fv of
    FunctionC f -> do
      let fID = functionUniqueId f
          fArgIds = map argumentUniqueId $ functionParameters f
          frmlActMap = IM.fromList $ [(fArgIds !! k, newId k) 
                                     | (av,k) <- argVars, length fArgIds >= k + 1]
                    ++ [(getNewId (valueUniqueId f) g, newId (g+10))| g <- glbIds]                 
          fPaSumm = IM.findWithDefault S.empty (functionUniqueId f) se
          glbActNodes = concat [ [(newId (g+10),ActualInNode iID g),
                  (newId' (g+10),ActualOutNode iID g)]| g <- glbIds]
          valActNodes = concat [ [(newId n,ActualInNode iID vi),
                   (newId' n,ActualOutNode iID vi)]| (vi,n) <- actValIDs]
          actualNodes = glbActNodes ++ valActNodes
          delOutIds = map negate . mapMaybe (flip IM.lookup frmlActMap). 
                         S.toList. S.map (negate. fst . fst) $ S.filter snd fPaSumm
          newNodes = IM.filterWithKey (\k _ -> notElem k delOutIds) $ IM.fromList actualNodes
          --
          newEdges = M.fromList $ fCallEdge: concat[fPaInEdge,fPaOutEdge,fActPaEdge,summaryEdge]  
            where fCallEdge = ((functionUniqueId f, iID), CallEdge)
                  fPaInEdge = [((a,c),ParaInEdge) | (a,c) <- IM.toList $ frmlActMap]
                  fPaOutEdge = [((-c,-a),ParaOutEdge) | (a,c) <- IM.toList $ frmlActMap]
                  fActPaEdge = [((c,iID),ControlDepEdge) | c <- IM.keys newNodes]  -- map fst actualNodes
                  !summaryEdge = [((toActNode a, toActNode b),SummaryEdge)
                                 | ((a,b),False) <- S.toList fPaSumm]
                     where toActNode ai = if ai < 0 
                                  then - IM.findWithDefault (-iID) (-ai) frmlActMap
                                  else IM.findWithDefault iID ai frmlActMap 
      return $ (edgeMap %~ M.union newEdges)
             $! (nodeMap %~ IM.union newNodes) si 
    ExternalFunctionC ef -> if not(isMemCMS fv) 
         then return $ (edgeMap %~ M.insert (efID,iID) CallEdge)
                     $! (nodeMap %~ IM.insert efID efNodeLab) si
         else return $ (edgeMap %~ M.union efEdges)
                     $! (nodeMap %~ IM.insert efID efNodeLab) si    
       where  efID = valueUniqueId ef
              efNodeLab = ExternalFunctionNode efID
              efEdges = M.fromList (efCallEdge : efParaEdges)  
              efCallEdge = ((efID, iID), CallEdge) 
              efParaEdges = if length cargs >= 2 then [efPaInEdge, efPaOutEdge] else []
              efPaInEdge = ((efID,valueUniqueId $ cargs !! 1),ParaInEdge)
              efPaOutEdge = ((valueUniqueId $ cargs !! 0, efID),ParaOutEdge)              
    _ -> return si