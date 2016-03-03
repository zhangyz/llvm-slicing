module LLVM.Slicing.Util.ValueMap where


import Control.Arrow
import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as M
import Data.Set ( Set )
import qualified Data.Set as S ( singleton,union )
import Data.IntMap.Strict ( IntMap )
import qualified Data.IntMap.Strict as IM
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM ( fromList )
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS
import Data.Maybe 
import Data.Monoid ( mempty )
import Data.List 
import qualified Data.Foldable as F ( foldr )

import LLVM.Analysis
import LLVM.Analysis.CFG  ( controlFlowGraph )
import LLVM.Analysis.CDG

import LLVM.Slicing.Util.Mix  




genValueMap :: Module -> IntMap Value
genValueMap m = {-# SCC genValueMap #-}  IM.fromList (zip allIds allVals)
  where   
    allVals = allValues m
    allIds = map valueUniqueId allVals
{-# INLINE genValueMap #-}


---
findVals :: IntMap Value -> IntSet -> [Value]
findVals m ks = IM.elems (IM.filterWithKey keyF m)
  where keyF k _ = IS.member k ks  

findVal = (^!)
(^!) :: IntMap Value -> UniqueId -> Value
m ^! k = IM.findWithDefault undef k m
  where undef = ConstantC UndefValue {constantType=TypeVoid, constantUniqueId = k}

--------    
genAliasMap :: Module -> Map String String
genAliasMap m = M.fromList $ glbAlias ++ concatMap getFunAlias fs
  where 
    glbAlias = [(show (globalAliasName ga), toVarName' (globalAliasTarget ga))
               | ga <- moduleAliases m ]
    fs = moduleDefinedFunctions m
    
genAliasMap' :: Module -> HashMap Value Value
genAliasMap' m = HM.fromList $ glbAlias ++ concatMap getFunAlias' fs
  where 
    glbAlias = [(toValue ga, globalAliasTarget ga) | ga <- moduleAliases m]
    fs = moduleDefinedFunctions m 
    
-----
genCtrDepMap :: Function -> IntMap ValueIds
genCtrDepMap f = IM.map IS.fromList . IM.fromList. map (instructionUniqueId &&& 
       (map instructionUniqueId . directControlDependencies cdg)) $ functionInstructions f
   where cdg = controlDependenceGraph $ controlFlowGraph f
{-# INLINE genCtrDepMap #-} 

