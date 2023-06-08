module Versao2 where

type State = String
type AtomicProgram = String
type NamedEdge = (State, State, AtomicProgram)
type Edge = (State, State)
type Graph = [NamedEdge]

data PDLProgram = AtomicProgram String | 
                  OperatorProgram String [PDLProgram] 
                  deriving Show

parsePDLProgram :: [String] -> (PDLProgram, [String])
parsePDLProgram ("U" : rest) =
  let (prog1, rest1) = parsePDLProgram rest
      (prog2, rest2) = parsePDLProgram rest1
  in (OperatorProgram "U" [prog1, prog2], rest2)
parsePDLProgram (";" : rest) =
  let (prog1, rest1) = parsePDLProgram rest
      (prog2, rest2) = parsePDLProgram rest1
  in (OperatorProgram ";" [prog1, prog2], rest2)
parsePDLProgram ("*" : rest) =
  let (prog, rest1) = parsePDLProgram rest
  in (OperatorProgram "*" [prog], rest1)
parsePDLProgram (token : rest) = (AtomicProgram token, rest)
parsePDLProgram [] = error "Empty program"

parsePDL :: [String] -> PDLProgram
parsePDL tokens =
  let (program, remainingTokens) = parsePDLProgram tokens
  in if null remainingTokens
      then program
      else error "Invalid program: Extra tokens remaining"

--Pegando todas as arestas quem contêm o atômico de entrada
getEdges :: Graph -> AtomicProgram -> [Edge]
getEdges graph labelEdge = 
  [(fromState, toState) | (fromState, toState, atomic) <- graph, atomic == labelEdge]

--Pegando arestas transitivas para a avaliação da sequência
getTransitiveEdges :: [Edge] -> [Edge] -> [Edge]
getTransitiveEdges edges1 edges2 =
   [(fromState1, toState2) | (fromState1, toState1) <- edges1, (fromState2, toState2) <- edges2, toState1 == fromState2]

evaluateProgram :: PDLProgram -> Graph -> (Bool, [Edge])
--caso atômico
evaluateProgram (AtomicProgram program) graph = 
  let edges = getEdges graph program
  in (edges /= [], edges)

evaluateProgram (OperatorProgram op [prog1, prog2]) graph = 
  case op of
    "U" -> evaluateNonDeterminism prog1 prog2 graph
    ";" -> evaluateSequence prog1 prog2 graph
    -- "*" -> evaluateIteration prog1 graph
    _ -> error "Invalid operator"

evaluateNonDeterminism :: PDLProgram -> PDLProgram -> Graph -> (Bool, [Edge])
evaluateNonDeterminism prog1 prog2 graph =
  let (result1, edges1) = evaluateProgram prog1 graph 
  --curto circuito, o primeiro basta
  in if result1
       then (result1, edges1)
       else evaluateProgram prog2 graph

evaluateSequence :: PDLProgram -> PDLProgram -> Graph -> (Bool, [Edge])
evaluateSequence prog1 prog2 graph = 
  let (result1, edges1) = evaluateProgram prog1 graph 
  in if result1
    then
      let (result2, edges2) = evaluateProgram prog2 graph 
      --Os dois deram verdadeiros
      in if result2 
        then (result2, getTransitiveEdges edges1 edges2)
      else (result2, edges2)
    else (result1, edges1)

-- evaluateIteration :: PDLProgram -> Graph -> (Bool, [Edge])
-- evaluateIteration prog graph = 
--   let (result, edges) =  evaluateProgram prog graph
--   in if result
--     then 

main = do
  let pdlProgram = words "; ; a b c"
  let programAST = parsePDL pdlProgram
  let graph = [("s1", "s2", "a"), ("s2", "s3", "b"), ("s3", "s4", "c")]
  let a = evaluateProgram programAST graph
  let convAtomicoA = parsePDL (words "a")
  let convAtomicoB = parsePDL (words "b")
  let (resultA, edgesA) = evaluateProgram convAtomicoA graph 
  let (resultB, edgesB) = evaluateProgram convAtomicoB graph
  let resultado = getTransitiveEdges edgesA edgesB
  print a
--   let isValid = evaluateProgram programAST graph
--   print programAST
--   putStrLn $ "Is graph valid for the program? " ++ show isValid
  