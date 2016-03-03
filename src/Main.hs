module Main where

import qualified Data.Map as M
import qualified Data.IntSet as IS  ( size )
import Options.Applicative

import LLVM.Slicing 

-----
---
data SliceMethod = Symbolic | SDG | Weiser | IFDS | Sym2
                  deriving (Read, Ord, Eq, Show)
data Direction = Fwd | Bwd | Both deriving (Read, Ord, Eq, Show)
data GrType = Sdg | Icfg | Cfg | Cdg | Cg | Pdt | Dt 
              deriving (Read, Ord, Eq, Show)

data Opts = Opts { 
                   criterion :: [String]
                 , direction :: Direction
                 , sliceMethod :: SliceMethod
                 , isParallel :: Bool
                 , timeOut :: Int
                 , grType :: Maybe GrType
                 , outputFile :: Maybe FilePath
                 , inputFile :: FilePath
                 } deriving (Show)

cmdOpts :: Parser Opts
cmdOpts = Opts
 <$> many (strOption
      ( long "criterion"
      <> short 'c'
      <> metavar "VARIABLES"
      <> help "The criterion variables (with the form of Var@Fun,e.g. x@main) for slicing. If null, just output the slice table for all single variables."))
  <*> option auto
      ( long "direction"
      <> short 'd'
      <> metavar "DIRECTION"
      <> help "The type of output to slice: Fwd, Bwd or Both. Default: Bwd"
      <> value Bwd)   
  <*> option auto
      ( long "method"
      <> short 'm'
      <> metavar "SLICE_METHOD"
      <> help "The slice algorithm: Symbolic,Weiser,SDG or IFDS. Default: Symbolic"
      <> value Symbolic)    
  <*> option auto
      ( long "isParallel"
      <> short 'p'
      <> metavar "ISPARALLEL"
      <> help "whether or not travelling SCC in callgraph in parallel. Default: False"
      <> value False)     
  <*> option auto
      ( long "timeout"
      <> short 't'
      <> metavar "TIMEOUT"
      <> help "The timeout (sec.) for running slicer. Default: 1800" 
      <> value 1800)  
  <*> optional (option auto
      ( long "graph"
      <> short 'g'
      <> metavar "GRAPH_SHOW"
      <> help "Print related graphs: Sdg,Cg,Cdg,Cfg,Icfg,Pdt or Dt." ))
  <*> optional (strOption
     ( long "output"
     <> short 'o'
     <> metavar "FILE/DIR"
     <> help "The destination of a file output"))
  <*> argument str 
      ( metavar "FILE" 
      <> help "The input file which can be bitcode,llvm assembly, or C/CPP sourcecode")
 
main :: IO ()
main = execParser args >>= realMain 
  where
    args = info (helper <*> cmdOpts)
      ( fullDesc
      <> progDesc "Generate program slices based on several methods for FILE (which can be bitcode,llvm assembly, or C/CPP sourcecode)"
      <> header "llvm-slicing -- Various program slicers based on LLVM")

realMain :: Opts -> IO ()
realMain opts = (timeoutWith (timeOut opts)). timeIO $! do
    let dir = direction opts
        inFile = inputFile opts
        outFile = outputFile opts
        sliceVars = criterion opts 
        method = sliceMethod opts
        isPar = isParallel opts
    m <- getModuleFromFile inFile
    let valMap = genValueMap m    
        (bwdSlices,fwdSlices) = genSliceTableWith (show method) isPar m                     
        res = if null sliceVars then tblRes  else sliRes 
        tblRes = case dir of 
           Fwd -> fwdTbl
           Bwd -> bwdTbl
           Both -> bwdTbl ++ "\n" ++ fwdTbl                   
          where bwdTbl = "\nBackward Static SliceTable:" ++ showSliSize bwdSlices 
                        ++ showSlices2 (toSrcLns bwdSlices)
                fwdTbl = "\nForward Static SliceTable:" ++ showSliSize fwdSlices 
                        ++ showSlices2 (toSrcLns fwdSlices)
                toSrcLns = M.map (toSrcLnStr valMap) 
                showSliSize s = "\n\t#Insts_sliced = " ++ show (allSlices s) 
                            ++ " (Average: " ++ show (avgSize s) ++ ")\n"    
                avgSize m = round $ (allSlices m)/(fromIntegral $ M.size m)  
                allSlices = fromIntegral . sum . map IS.size . M.elems           
        sliRes = case dir of
           Fwd -> fwdSli
           Bwd -> bwdSli
           Both -> bwdSli ++ "\n" ++ fwdSli                   
          where bwdSli = "Backward Static Slice for " ++ show sliceVars ++ showIRSli bwdSlices
                fwdSli = "Forward Static Slice for " ++ show sliceVars ++ showIRSli fwdSlices  
                              
        showIRSli slices = ":\n" ++ srcLines ++ valStrings  --  show vals
          where vals = unionLkpSli sliceVars  slices
                srcLines = " <SourceLines> " ++ show (toSrcLnStr valMap vals) ++ ": \n"
                valStrings = concatMap showVal (findVals valMap vals)
                showVal v = "  " ++ show v ++ "\n" 

    case outFile of  
      Nothing -> writeFile fn res
               where fn = inFile ++ ".SliceResult_" ++ show dir ++ "-" ++ show method 
      Just ofile -> appendFile ofile res
    putStrLn res   
    printInfo m

 
