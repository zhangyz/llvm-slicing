module LLVM.Slicing.Util.InOutPut where


import Data.Maybe 
import System.Timeout
import Data.Time
import Data.Char ( isLetter )

import LLVM.Analysis
--import LLVM.Analysis.CFG  
import LLVM.Analysis.Util.Testing
import LLVM.Parse

import LLVM.Slicing.Util.SrcLineNum ( valueLine )
import LLVM.Slicing.Util.ValueTest ( isAllocaInst )
import LLVM.Slicing.Util.Mix  ( memAccessBase,funcAllocInsts,toVarName' )


timeIO :: IO () -> IO ()
timeIO ioa = do
    t1 <- getCurrentTime
    ioa 
    t2 <- getCurrentTime
    putStrLn $! "\tIts runtime = " ++ show (realToFrac $ diffUTCTime t2 t1)

timeoutWith :: Int -> IO a -> IO ()
timeoutWith sec_time action = do
    result <- timeout (10^6 * sec_time) action
    case result of
      Just result -> return ()
      Nothing     -> putStrLn $ "time limit exceeded after " ++ show sec_time ++ "sec." 

----
getModuleFromFile :: FilePath -> IO Module
getModuleFromFile fn = buildModule ["-g"] optOptions toModule fn
   where optOptions = ["-gvn", "-basicaa"]     -- ["-mem2reg", "-gvn"] 
         toModule = parseLLVMFile defaultParserOptions
     
            
printInfo :: Module -> IO ()
printInfo m = putStrLn info 
  where 
    fs = moduleDefinedFunctions m
    allBlocks = concatMap functionBody fs
    allInsts = concatMap basicBlockInstructions allBlocks
    ctrInsts = mapMaybe ctrCondValue allInsts
    allocInsts = filter isAllocaInst allInsts        
    allVals =  map toValue (concatMap functionParameters fs)
            ++ map toValue (moduleGlobalVariables m) 
            ++ map toValue (concatMap funcAllocInsts fs)
    allVals' = filter ((\(k:_)->(isLetter k || k == '_')). drop 1. toVarName') allVals
    fnSize = "\n\t#Defined_Functions = " ++ (show $ length fs)
--    cfgSize = "\n\tCFG(#Nodes,#Edges) = " ++ show (map cfgInfo fs) 
    blkSize = "\n\t#BasicBlocks = " ++ (show $ length allBlocks)  
    instSize = "\n\t#Insts_All = " ++ (show $ length allInsts)
    ctrSize = "\n\t  #Insts_br = " ++ (show $ length ctrInsts)
    varSize = "\n\t  #Insts_alloc = " ++ (show $ length allocInsts)
    varSliced = "\n\t#Vars_sliced = " ++ show (length allVals')
    info = concat ["\nIts some statistic Info.:",
            fnSize,blkSize,instSize,varSize,ctrSize,varSliced,"\n\n"]

ctrCondValue :: Instruction -> Maybe (Instruction,Value)
ctrCondValue i@BranchInst {branchCondition = c} = Just (i,c)
ctrCondValue i@SwitchInst {switchValue = v} = Just (i,v)
ctrCondValue i@IndirectBranchInst {indirectBranchAddress = a} = Just (i,memAccessBase a)
ctrCondValue i@SelectInst {selectCondition = c} = Just (i,c)
ctrCondValue _  = Nothing    


