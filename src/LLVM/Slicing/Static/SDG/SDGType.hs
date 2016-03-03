{-# LANGUAGE OverloadedStrings,TemplateHaskell,TypeSynonymInstances,FlexibleInstances,DeriveGeneric #-}
module LLVM.Slicing.Static.SDG.SDGType (
  -- * Types
  SDGEdge(..),
  SDGNode(..),  SDGNode2(..),
  SDGGraphType, SDGGraphType2(..),
  -- * Constructor
  getUID,
  convertNode, convertNode2,
  insEdges2,
  -- * Visualization
  sdgGraphvizRepr
  ) where

import Data.Graph.Inductive  
import Data.GraphViz  
import GHC.Generics ( Generic )
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import qualified Data.Text.Lazy as L ( pack )
import Debug.Trace.LocationTH  ( failure )
import Text.Printf  ( printf )
import Data.Maybe
import Data.List  ( nub )
import qualified Data.Foldable as F  ( foldr' )
import qualified Data.Set as S

import LLVM.Analysis

import LLVM.Slicing.Util.Utils  ( toValName,valueLine )



data  SDGNode = InstructionNode UniqueId
              | ActualInNode UniqueId UniqueId
              | ActualOutNode UniqueId UniqueId
              | FormalInNode UniqueId
              | FormalOutNode UniqueId
              | GlobalVariableInNode UniqueId UniqueId
              | GlobalVariableOutNode UniqueId UniqueId
              | FunctionEntryNode UniqueId
              | ExternalFunctionNode UniqueId
              | FinalUseNode UniqueId
              deriving (Show,Eq,Ord,Generic)   

data  SDGEdge = CallEdge 
              | ParaInEdge
              | ParaOutEdge
              | ControlDepEdge
              | DataDepEdge
              | SummaryEdge
              deriving (Show,Eq,Ord,Generic)

instance Labellable SDGNode where
  toLabelValue = toLabelValue . show

instance Labellable SDGEdge where
  toLabelValue = toLabelValue . show

instance NFData SDGNode where
  rnf = genericRnf

instance NFData SDGEdge where
  rnf = genericRnf

type SDGGraphType = Gr SDGNode SDGEdge


instance Ord SDGGraphType where
  compare g1 g2 = compare (noNodes g1) (noNodes g2)

instance NFData SDGGraphType where
  rnf g = g `seq` ()  


convertNode :: (Int -> Value) -> SDGNode -> Value
convertNode i2v = i2v . getUID

getUID :: SDGNode -> UniqueId
getUID (InstructionNode i) = i
getUID (ActualInNode i v) = v
getUID (ActualOutNode i v) = v
getUID (FormalInNode a) = a
getUID (FormalOutNode a) = a
getUID (FunctionEntryNode f) = f
getUID (ExternalFunctionNode f) = f
getUID (GlobalVariableInNode f g) = g
getUID (GlobalVariableOutNode f g) = g
getUID (FinalUseNode u) = u

--- Visual
data SDGNode2 = InstNode Instruction
              | ActInNode Instruction Value
              | ActOutNode Instruction Value
              | FmlInNode Argument
              | FmlOutNode Argument
              | GlobalVarInNode Function GlobalVariable
              | GlobalVarOutNode Function GlobalVariable
              | FunEntryNode Function
              | ExtFunNode ExternalFunction
              | FUseNode Instruction

instance Show SDGNode2 where
  show (InstNode i) = show (valueLine i) ++ ":" ++ show i
  show (ActInNode i v) = printf "(actual-in)%s:%s" (toValName i)(toValName v)
  show (ActOutNode i v) = printf "(actual-out)%s:%s" (toValName i)(toValName v)
  show (FmlInNode a) = printf "(formal-in)%s" . show . argumentName $ a
  show (FmlOutNode a) = printf "(formal-out)%s". show . argumentName $ a
  show (FunEntryNode f) = printf "ENTER %s". show . functionName $ f  
  show (ExtFunNode ef) = printf "Extern %s". show . externalFunctionName $ ef
  show (GlobalVarInNode f g) = printf "(global-in)%s:%s" (show $ functionName f)
                                           (show $ globalVariableName g)
  show (GlobalVarOutNode f g) = printf "(global-out)%s:%s" (show $ functionName f)
                                           (show $ globalVariableName g)
  show (FUseNode u) = printf "FinalUse(%s)". toValName $ u

convertNode2 :: (Int -> Value) -> SDGNode -> SDGNode2
convertNode2 i2v (InstructionNode i) = InstNode (toInst $ i2v i)
   where  toInst v = case valueContent' v of
               InstructionC iv -> iv
               _ -> $failure "convertNode:InstructionNode"
convertNode2 i2v (ActualInNode i v) = 
    ActInNode (toInst $ i2v i) (i2v v)
   where  toInst v = case valueContent' v of
               InstructionC iv -> iv
               _ -> $failure "convertNode:ActualInNode"  
convertNode2 i2v (ActualOutNode i v) =  
    ActOutNode (toInst $ i2v i) (i2v v)
   where  toInst v = case valueContent' v of
               InstructionC iv -> iv
               _ -> $failure "convertNode:ActualOutNode"
convertNode2 i2v (FormalInNode a) = FmlInNode (toArg $ i2v a)
   where  toArg v = case valueContent' v of
               ArgumentC ia -> ia
               _ -> $failure "convertNode:FormalInNode"
convertNode2 i2v (FormalOutNode a) = FmlOutNode (toArg $ i2v a)
   where  toArg v = case valueContent' v of
               ArgumentC ia -> ia
               _ -> $failure "convertNode:FormalOutNode"
convertNode2 i2v (GlobalVariableInNode f g) = GlobalVarInNode func glb
   where fv = valueContent' $ i2v f
         gv = valueContent' $ i2v g 
         (func,glb) = case (fv,gv) of
            (FunctionC fi, GlobalVariableC gi) -> (fi,gi)
            _ -> $failure "convertNode:GlobalVariableInNode"
convertNode2 i2v (GlobalVariableOutNode f g) = GlobalVarOutNode func glb
   where fv = valueContent' $ i2v f
         gv = valueContent' $ i2v g 
         (func,glb) = case (fv,gv) of
            (FunctionC fi, GlobalVariableC gi) -> (fi,gi)
            _ -> $failure "convertNode:GlobalVariableOutNode"
convertNode2 i2v (FunctionEntryNode f) = FunEntryNode (toFunc $ i2v f)
   where  toFunc v = case valueContent' v of
               FunctionC fi -> fi
               _ -> $failure "convertNode:FunctionEntryNode"
convertNode2 i2v (ExternalFunctionNode f) = ExtFunNode (toFunc $ i2v f)
   where  toFunc v = case valueContent' v of
               ExternalFunctionC ef ->  ef
               _ -> $failure "convertNode:ExternalFunctionNode"
convertNode2 i2v (FinalUseNode i) = FUseNode (toInst $ i2v i)
   where  toInst v = case valueContent' v of
               InstructionC iv -> iv
               _ -> $failure "convertNode:FinalUseNode"

type SDGGraphType2 = Gr SDGNode2 SDGEdge 

data SDGCluster = CUnknown
                | CFunction !Function
                | CGlobalVariable 
                deriving (Eq, Ord)

clusterIdent :: SDGCluster -> GraphID
clusterIdent CUnknown = Str (L.pack "unknown")
clusterIdent (CFunction f) = Num. Int $ functionUniqueId f     -- Num.
clusterIdent (CGlobalVariable) = Str (L.pack "global")

instance Show SDGCluster where
  show CUnknown = "Unknown"
  show (CFunction f) = show (functionName f)
  show CGlobalVariable = "GlobalVariable"  

sdgParams :: GraphvizParams Node SDGNode2 SDGEdge SDGCluster SDGNode2 
sdgParams =
  defaultParams { fmtNode = formatNode
                , fmtEdge = formatEdge
                , clusterBy = nodeCluster
                , clusterID = clusterIdent
                , fmtCluster = formatCluster
                }
  where
    formatCluster CUnknown = [GraphAttrs [textLabel $ L.pack "UnknownFunction"]]
    formatCluster (CFunction f) = [GraphAttrs { attrs = [toLabel (show (functionName f))]} ]
    formatCluster CGlobalVariable = [GraphAttrs [textLabel $ L.pack "GlobalVariable"] ]
    nodeCluster l@(_, InstNode i) = case instructionFunction i of
       Nothing -> C CUnknown (N l)
       Just f  -> C (CFunction f) (N l)
    nodeCluster l@(_, ActInNode i v) = case instructionFunction i of
       Nothing -> C CUnknown (N l)
       Just f  -> C (CFunction f) (N l)
    nodeCluster l@(_, ActOutNode i v) = case instructionFunction i of
       Nothing -> C CUnknown (N l)
       Just f  -> C (CFunction f) (N l)
    nodeCluster l@(_, FmlInNode a) = C (CFunction f) (N l)
       where  f = argumentFunction a
    nodeCluster l@(_, FmlOutNode a) = C (CFunction f) (N l)
       where  f = argumentFunction a
    nodeCluster l@(_, FunEntryNode f) = C (CFunction f) (N l)
    nodeCluster l@(_, ExtFunNode ef) = C CUnknown (N l)
    nodeCluster l@(_, GlobalVarInNode f g) = C (CFunction f) (N l)  -- (C CGlobalVariable (N l))
    nodeCluster l@(_, GlobalVarOutNode f g) = C (CFunction f) (N l) -- (C CGlobalVariable (N l))
    nodeCluster l@(_, FUseNode i) = case instructionFunction i of
       Nothing -> C CUnknown (N l)
       Just f  -> C (CFunction f) (N l)
    formatNode (_,l) = case l of
        InstNode i -> [toLabel (show (valueLine i) ++ ": " ++ show i), shape BoxShape]
        FUseNode i -> [toLabel (show l), color Green]
        _ -> [toLabel (show l),color Yellow]
    formatEdge (_,_,l) = case l of
        CallEdge -> [color DeepSkyBlue]
        ParaOutEdge -> [style dashed, color Purple]   -- Crimson
        ParaInEdge -> [style dashed, color ForestGreen]
        ControlDepEdge -> [color Black]
        DataDepEdge  -> [color SandyBrown]
        SummaryEdge  -> [color Red, style bold]       -- style dotted

sdgGraphvizRepr :: SDGGraphType2 -> DotGraph Node
sdgGraphvizRepr = graphToDot sdgParams 

instance ToGraphviz SDGGraphType2 where
  toGraphviz = sdgGraphvizRepr

-----------------------------------------------------
---
insEdges2 :: (Show b, DynGraph gr, Ord b) => [LEdge b] -> gr a b -> gr a b
insEdges2 es g = S.foldr' insEdge2 g $ S.fromList es 
  where 
    insEdge2 :: (Show b, DynGraph gr) => LEdge b -> gr a b -> gr a b
    insEdge2 n@(v,w,l) g = 
        case (gelem v g,gelem w g) of
        (True,True) -> insEdge n g
        _  -> g
{-# INLINE insEdges2 #-}

