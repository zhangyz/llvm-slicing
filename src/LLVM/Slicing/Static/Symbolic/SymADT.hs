{-# LANGUAGE BangPatterns,ViewPatterns,DeriveGeneric,NoMonomorphismRestriction,TemplateHaskell #-}

module LLVM.Slicing.Static.Symbolic.SymADT where

import GHC.Generics ( Generic )
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( makeLenses, (%~), (^.) )
import Control.Monad.RWS.Strict (RWS)
import qualified Control.Monad.RWS.Strict as RW

import qualified Data.Map as M
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import qualified Data.HashSet as HS
import qualified Data.IntSet as IS
import Data.Maybe  

import LLVM.Analysis

import LLVM.Slicing.Util.Utils
import LLVM.Slicing.Data.SliceType     



----
data SliceEnv = SEnv { procSliTbl :: !(IntMap SliceTable)  
                     , procInstDep :: IntMap (IntMap ValueIds)
                     , paraValMap :: !(IntMap (Value,Int))
                     , instCtrMap :: IntMap ValueIds
                     }                      

data SliceState = SState { traces :: !Int      --  [Instruction]
                         , instDepMap :: IntMap ValueIds
                         } deriving (Generic)

data SliceInfo = SInfo { _sliceTable :: !SliceTable   
                       , _ctrDeps :: IntMap ValueIds  
                       }
              deriving (Eq,Ord,Show,Generic)

$(makeLenses ''SliceInfo)

instance NFData SliceState where
  rnf = genericRnf

instance NFData SliceInfo where
  rnf = genericRnf
  


----------------------------------------------
---
type Analysis = RWS SliceEnv String SliceState

runAnalysis :: RWS r b s a -> r -> s -> a 
runAnalysis a r s = fst $ RW.evalRWS a r s
analysisEnvironment = RW.asks
analysisGet = RW.get
analysisPut = RW.put
analysisLocal = RW.local
  

     
----------------------------------
------
unionLs :: IsValue a => IntMap ValueIds -> SliceInfo -> Instruction -> a -> ValueIds
unionLs cdM si i v = unionL' l l0 (v,ss)
  where !l0 = findCD cdM si i  
        iID = instructionUniqueId i 
        !l = IS.insert iID $ lkpCtrDep i si     
        ss = si ^. sliceTable
{-# INLINE unionLs #-}

unionL' :: IsValue a => ValueIds -> ValueIds -> (a,SliceTable) -> ValueIds
unionL' l l0 (i,s) = IS.unions [l, l0, refIds, unionLkpSli refStrs s]
  where !refValues = refVals i
        !refIds = IS.fromList . HS.toList . HS.map valueUniqueId $ refValues 
        !refStrs = mapMaybe toVarName . HS.toList $ refValues    
{-# INLINE unionL' #-}

setTrInstCtrDep :: IntMap ValueIds -> SliceInfo -> Instruction -> Analysis SliceInfo  
setTrInstCtrDep cdM si i = do
  SState tr idM <- analysisGet
  let !l' = unionLs cdM si i i
      iID = instructionUniqueId i
      tr' = 1 + tr
      idM' = IM.insert iID l' idM       
      !si' = addInstDep iID l' si
  analysisPut (SState tr' idM')
  return si' 

setTrInstDep :: IntMap ValueIds -> SliceInfo -> Instruction -> Analysis SliceInfo  
setTrInstDep cdM si i = do
  SState tr idM <- analysisGet
  let !l' = unionLs cdM si i i
      iID = instructionUniqueId i
      tr' = 1 + tr
      idM' = IM.insert iID l' idM       
  analysisPut (SState tr' idM')
  return si 


addTrInstDep :: SliceInfo -> Instruction -> ValueIds -> Analysis SliceInfo
addTrInstDep si i l' = do 
  SState tr idM <- analysisGet
  let iID = instructionUniqueId i
      tr' = 1 + tr
      idM' = IM.insert iID l' idM      
  analysisPut (SState tr' idM')  
  return si 


addInstDep :: UniqueId -> ValueIds -> SliceInfo -> SliceInfo
addInstDep n d = ctrDeps %~ IM.insert n d    
{-# INLINE addInstDep #-}

lkpCtrDep ::  Instruction -> SliceInfo -> ValueIds
lkpCtrDep i si = 
   IM.findWithDefault IS.empty (instructionUniqueId i) $ si ^. ctrDeps
{-# INLINE lkpCtrDep #-}

findCD ::  IntMap ValueIds -> SliceInfo -> Instruction -> ValueIds
findCD cdM si i = cds
  where cds = IS.unions [lkpCD ci | ci <- IS.toList cis]
        lkpCD n = IM.findWithDefault IS.empty n $ si ^. ctrDeps
        cis = IM.findWithDefault IS.empty (instructionUniqueId i) cdM
{-# INLINE findCD #-}

---
getTrace :: Analysis Int -- [Instruction]
getTrace = do {s <- analysisGet; return (traces s) }  

addTrace :: Instruction -> Analysis ()
addTrace i = do 
  s <- analysisGet  
  let tr' = 1 + traces s   
  analysisPut s { traces = tr'}

getInstDep :: Analysis (IntMap ValueIds)  
getInstDep = do {s <- analysisGet; return (instDepMap s) }  

setInstDep :: IntMap ValueIds -> Analysis ()
setInstDep idM = do 
  s <- analysisGet  
  let idM' = IM.unionWith IS.union idM (instDepMap s)
  analysisPut s {instDepMap = idM'}




      


    


