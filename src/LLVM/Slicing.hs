module LLVM.Slicing (
  -- * Types
  module LLVM.Slicing.Static.SDG.SDGType,
  module LLVM.Slicing.Data.SliceType,  
  module LLVM.Slicing.Util.Utils,
  -- * Slice operators 
  genSliceTableWith,
  compareSliceTable,
  -- * Show SDG graph
  genSDGgraph
 ) where

import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.IntSet as IS
import Text.Printf  ( printf )
import Data.Char ( isLetter )
import Data.Maybe ( maybeToList )

import qualified Data.Text.Lazy as L ( unpack )
import qualified Data.Graph.Inductive as G ( grev,nmap )
import qualified Data.GraphViz as G  ( printDotGraph ) 

import LLVM.Analysis 


import LLVM.Slicing.Util.Utils
import LLVM.Slicing.Data.SliceType 
import LLVM.Slicing.Static.SDG.SDGType 
import qualified LLVM.Slicing.Static.Symbolic.SymSlicer as Sym
import qualified LLVM.Slicing.Static.SDG.SDGSlicer as SDG
-- import qualified LLVM.Slicing.Static.SDG.IFDS.IFDSSlicer as IFDS
import qualified LLVM.Slicing.Static.Weiser.MWeiser as MW

    
-- | Get backward/forward slice tables with a given method
genSliceTableWith :: String -> Bool -> Module -> (SliceTable,SliceTable)
genSliceTableWith method isPar m
  | elem method ["sym","symbolic","Symbolic","Sym","SymSlicer"] = Sym.genSliceTable isPar m
  | elem method ["sdg","SDG","SDGSlicer","sdgSlicer"] =  SDG.genSliceTable isPar m
-- | elem method ["ifds","IFDS","IFDSSlicer","ifdsSlicer"] =  IFDS.genSliceTable isPar m
  | elem method ["weiser","Weiser","MWeiser","WeiserSlicer"] =  
        if isPar then error "Weiser cann't support to compute slices parallelly!" 
        else MW.genSliceTable m
  | otherwise  = error "Unknown the slice method (Symbolic,SDG,IFDS or Weiser)!"

  
-- | Compare two slice tables
compareSliceTable :: Module -> SliceTable -> SliceTable 
                      -> (M.Map String [String],M.Map String [String])  
compareSliceTable m st1 st2 = (toSrcLns $ diffSli st1, toSrcLns $ diffSli st2)
  where  
    allFunIds = IS.fromList $ map valueUniqueId (moduleDefinedFunctions m) 
                           ++ map valueUniqueId (moduleExternalFunctions m)
    bothSli = M.intersectionWith IS.intersection st1 st2  
    diffSli st = M.differenceWith mapF st bothSli
    mapF s1 s2 = let s' = s1 IS.\\ s2 IS.\\ allFunIds in
                 if IS.null s' then Nothing else Just s' 
    valMap = genValueMap m
    toSrcLns = M.map (toSrcLnStr valMap)
    
-- | Generate a SDG graph
genSDGgraph :: Module -> String
genSDGgraph m = toDotString (G.grev sdg')
  where
    valMap = genValueMap m    
    sdg' = G.nmap (convertNode2 (valMap ^!)) sdg 
    sdg = SDG.genSDG False m      -- IFDS.genSDG False m 
       
toDotString :: ToGraphviz a => a -> String    
toDotString = L.unpack . G.printDotGraph . toGraphviz 
