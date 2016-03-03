{-# LANGUAGE FlexibleInstances,TypeSynonymInstances,MultiParamTypeClasses,NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -XUndecidableInstances #-}

module LLVM.Slicing.Data.SliceType ( 
  -- * Types
  LabelType, LabelSet, 
  SliceTable, 
  -- * Constructor
  lkpSli, mrgSli,
  updSli, updSli2, updSlices,  
  xtdSli, xtdSli2, xtdSlices,    
  unionLkpSli, 
  -- * Visualization
  showSlices, showSlices2
  )
 where
 
import Data.List (delete,foldl',intersperse) 
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map


type Name = String
type LabelType = Int
type LabelSet = IntSet  
type SliceTable = Map Name LabelSet 


instance {-# OVERLAPPING #-} Show SliceTable where
 show ds = showSlices ds
 
showSlices :: SliceTable -> String
showSlices = showSlices' IntSet.toList
showSlices2 = showSlices' id

showSlices' toList ds | ds == Map.empty = "\nThe slice table is NULL !" 
                      | otherwise = "\n Variable      SrcLineNumbers  "  ++ 
                                    "\n------------------------------\n" ++ res
   where res = unlines . buildTable $ mapSnds (concat. (intersperse ","). (map show). toList) ds'
         ds' = Map.toAscList ds
         mapSnds g xs = [(x, g y) | (x,y) <- xs]


-- | lkpSli n ds = list of labels that reference n in ds
lkpSli :: Name -> SliceTable -> LabelSet
lkpSli x ls =  {-# SCC lkpSli #-} Map.findWithDefault IntSet.empty x ls
{-# INLINE lkpSli #-}

-- | updSli n ls ds = updates ds assigning ls to n
-- {-# SCC "updSlice" #-}
updSli :: Name -> LabelSet -> SliceTable -> SliceTable
updSli =  Map.insert   

updSli2 :: [Name] -> LabelSet -> SliceTable -> SliceTable           
updSli2 args ls ds
           = foldl'
              (\r arg -> updSli arg ls r) ds args

updSlices :: [Name] -> [LabelSet] -> SliceTable -> SliceTable
updSlices args [] ds = ds
--           = foldl'
--              (\r arg -> updSli arg IntSet.empty r) ds args              
updSlices args lcs ds
           = foldl'
              (\r (arg,lc)-> updSli arg lc r) ds
                [(arg,lc) | (arg,lc) <- zip args lcs]

-- | xtdSli n ls ds = extends ds assigning ls to n
xtdSli :: Name -> LabelSet -> SliceTable -> SliceTable
xtdSli = Map.insertWith' IntSet.union 
    
xtdSli2 :: [Name] -> LabelSet -> SliceTable -> SliceTable
xtdSli2 args ls ds
           = foldl'
              (\r arg -> xtdSli arg ls r) ds args

xtdSlices :: [Name] -> [LabelSet] -> SliceTable -> SliceTable
xtdSlices args [] ds = ds
--           = foldr(\arg r -> xtdSli arg IntSet.empty r) ds args
xtdSlices args lcs ds
           = foldl'
              (\r (arg,lc) -> xtdSli arg lc r) ds
                [(arg,lc) | (arg,lc) <- zip args lcs]
              
-- | mrgSli ss ss' = merges two slices ss and ss'
mrgSli ::  SliceTable -> SliceTable -> SliceTable
mrgSli = {-# SCC mrgSli #-} Map.unionWith IntSet.union
{-# INLINE mrgSli #-}


unionLkpSli :: [Name] -> SliceTable -> LabelSet
unionLkpSli vs ls = {-# SCC unionLkpSli #-} 
    IntSet.unions [lkpSli v ls | v <- vs]    
{-# INLINE unionLkpSli #-}
 

------- Utils
buildTable :: [(String,String)] -> [String]
buildTable ps = map f ps where
    f (x,y) = " " ++ x ++ replicate (bs - length x) ' ' 
              ++ replicate 8 ' ' ++ "{" ++ y ++ "}"
    bs = maximum (map (length . fst) ps)


------- Test
s1 :: SliceTable
s1 = Map.fromList [("ta",IntSet.fromList [1]),("bd",IntSet.fromList [1,3,2,3,4,4,4,4,4,4]),
      ("0cd",IntSet.fromList [2,3,1]),("d",IntSet.fromList [4])]

s2 = updSli2 ["ta","hello"] IntSet.empty s1


