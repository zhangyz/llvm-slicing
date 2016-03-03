{-# LANGUAGE BangPatterns,ViewPatterns #-}


module LLVM.Slicing.Util.SrcLineNum where

import Data.IntMap.Strict ( IntMap )
import qualified Data.IntMap.Strict as IM
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS ( member )
import Data.Maybe 
import Data.List 
import Data.Char ( isSpace )
import qualified Data.Text as T (unpack)
--import qualified Data.Text.Lazy as L ( unpack,pack )
import Text.Printf ( printf )
import System.IO.Unsafe ( unsafePerformIO )

import LLVM.Analysis

import LLVM.Slicing.Util.Mix  ( groupFst,sortFst )



toSrcLnStr :: IntMap Value -> IntSet -> [String]    
toSrcLnStr vm = map mergSrc. groupFst. sortFst. mapMaybe valueSrcLn. findVals vm
  where mergSrc :: [(String,[Int])] -> String   
        mergSrc [] = ""
        mergSrc ss = hd ++ ": " ++ show lns   -- show lns ++ "@" ++ hd
         where hd = fst (head ss)
               lns = nub . sort $ concatMap snd ss          
        --
        findVals :: IntMap Value -> IntSet -> [Value]
        findVals m ks = IM.elems (IM.filterWithKey keyF m)
          where keyF k _ = IS.member k ks  

--------
valueLine :: IsValue a => a -> [Int] 
valueLine = mapMaybe metadataToLine . valueMetadata

metadataToLine :: Metadata -> Maybe Int
metadataToLine md@MetaSourceLocation { } = Just . fromIntegral . metaSourceRow $ md
metadataToLine md@MetaDWSubprogram {} = Just . fromIntegral . metaSubprogramLine $ md
metadataToLine md@MetaDWLexicalBlock { } = Just . fromIntegral . metaLexicalBlockRow $ md
metadataToLine md@MetaDWVariable {} = Just . fromIntegral . metaGlobalVarLine $ md
metadataToLine md@MetaDWBaseType {} = Just . fromIntegral . metaBaseTypeLine $ md
metadataToLine md@MetaDWDerivedType {} = Just . fromIntegral . metaDerivedTypeLine $ md
metadataToLine md@MetaDWCompositeType {} = Just . fromIntegral . metaCompositeTypeLine $ md
metadataToLine md@MetaDWLocal {} = Just . fromIntegral . metaLocalLine $ md
metadataToLine md@MetaDWNamespace {} = Just . fromIntegral . metaNamespaceLine $ md
metadataToLine md@MetaDWTemplateTypeParameter {} = 
       Just . fromIntegral . metaTemplateTypeParameterLine $ md
metadataToLine md@MetaDWTemplateValueParameter {} = 
       Just . fromIntegral . metaTemplateValueParameterLine $ md
metadataToLine _ = Nothing


----
valueSrcLn :: IsValue a => a -> Maybe (FilePath, [Int])   -- [Int]
valueSrcLn v = do
  func <- valueFunction v
  let mds = filter isSubprogramMetadata $ functionMetadata func
      line = valueLine v
  case mds of
    [md] -> do
      ctxt <- metaSubprogramContext md
      let f = metaFileSourceFile ctxt
          d = metaFileSourceDir ctxt
          absSrcFile = T.unpack f  -- (T.unpack d) </> (T.unpack f)
      return (absSrcFile, line)  
    _ -> Nothing
  where
    isSubprogramMetadata :: Metadata -> Bool
    isSubprogramMetadata MetaDWSubprogram {} = True
    isSubprogramMetadata _ = False

valueFunction :: IsValue a => a -> Maybe Function
valueFunction v = case valueContent v of
    FunctionC f -> Just f
    ArgumentC a -> Just (argumentFunction a)
    BasicBlockC b -> Just (basicBlockFunction b)
    InstructionC i -> instructionFunction i
    _ -> Nothing



