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

-- Lendo o grafo, descomentar na main
readGraph :: Graph -> IO Graph
readGraph lines = do
    line <- getLine
    if line == "0"
        then return lines
        else do 
            let [fromState, toState, labelEdge] = words line
            readGraph((fromState, toState, labelEdge) : lines)

--Pegando todas as arestas quem contêm o atômico de entrada
getEdges :: Graph -> AtomicProgram -> [Edge]
getEdges graph labelEdge = 
  [(fromState, toState) | (fromState, toState, atomic) <- graph, atomic == labelEdge]

--Pegando arestas transitivas para a avaliação da sequência
getTransitiveEdges :: [Edge] -> [Edge] -> [Edge]
getTransitiveEdges edges1 edges2 =
   [(fromState1, toState2) | (fromState1, toState1) <- edges1, (fromState2, toState2) <- edges2, toState1 == fromState2]

-- Pega as relações transitivas mais longas e independentes
-- Para a entrada [("1", "2"), ("2", "3"), ("3", "4"), ("4", "5"), ("5", "6"), ("6", "90"), ("7", "8"), ("8", "9"), ("9", "10"), ("10", "11"), ("11", "12"), ("23", "34"), ("34", "85")]
-- A saída é [("1","90"),("7","12"),("23","85")]
getMaxTransitives :: [Edge] -> [Edge] -> [Edge]
getMaxTransitives [] outEdges = outEdges
getMaxTransitives edges outEdges =
  let ((fromState, toState), updatedEdges) = getMaxTransitive (head edges) (tail edges)
  in getMaxTransitives updatedEdges (outEdges ++ [(fromState, toState)])

getMaxTransitive :: Edge -> [Edge] -> (Edge, [Edge])
getMaxTransitive edge edges =
  let (fromState, toState) = edge
      (toState', toState2) = case filter (\(initialState, _) -> initialState == toState) edges of
                    [] -> ("", "")
                    ((_, finalState):_) -> (toState, finalState)
      updatedEdges = filter (\(initialState, _) -> initialState /= toState) edges
  in
    if toState' == ""
      then (edge, edges)
      else getMaxTransitive (fromState, toState2) updatedEdges

evaluateProgram :: PDLProgram -> Graph -> (Bool, [Edge])
--caso atômico
evaluateProgram (AtomicProgram program) graph = 
  let edges = getEdges graph program
  in (edges /= [], edges)
evaluateProgram (OperatorProgram op [prog1, prog2]) graph = 
  case op of
    "U" -> evaluateNonDeterminism prog1 prog2 graph
    ";" -> evaluateSequence prog1 prog2 graph
evaluateProgram (OperatorProgram op [prog]) graph = 
  if op == "*" 
    then evaluateIteration prog graph
    else error "Invalid operator"

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
      (result2, edges2) = evaluateProgram prog2 graph
  in if result1 && edges1 == []
    then (result2, edges2)
    else if result2 && edges2 == []
      then (result1, edges1)
      else 
        let transitiveEdges = getTransitiveEdges edges1 edges2
        in (result1 && result2 && transitiveEdges /= [], transitiveEdges)
            

evaluateIteration :: PDLProgram -> Graph -> (Bool, [Edge])
evaluateIteration prog graph =
  let (result, edges) =  evaluateProgram prog graph
  in (True, getMaxTransitives edges [])

main = do
  let pdlProgram = words "; U ; a b c * d"
  let programAST = parsePDL pdlProgram
  
  let graph1 = [("s1", "s2", "c")]
  let graph2 = [("s1", "s2", "a"), ("s2", "s3", "b")]
  let graph3 = [("s1", "s2", "a"), ("s2", "s3", "b"), ("s3", "s4", "d"), ("s4", "s5", "k")]
  let graph4 = [("s1", "s2", "c"), ("s2", "s3", "d"), ("s3", "s4", "p")]
  let graph5 = [("s1", "s2", "a"), ("s2", "s3", "b"), ("s3", "s4", "k"), ("s4", "s5", "d")]
  let graph6 = [("s1", "s2", "a"), ("s2", "s3", "b"), ("s3", "s4", "k")]

  putStrLn ("O resultado do caso 1 é: " ++ show (evaluateProgram programAST graph1))
  putStrLn ("O resultado do caso 2 é: " ++ show (evaluateProgram programAST graph2))
  putStrLn ("O resultado do caso 3 é: " ++ show (evaluateProgram programAST graph3))
  putStrLn ("O resultado do caso 4 é: " ++ show (evaluateProgram programAST graph4))
  putStrLn ("O resultado do caso 5 é: " ++ show (evaluateProgram programAST graph5))
  putStrLn ("O resultado do caso 6 é: " ++ show (evaluateProgram programAST graph6))

  -- lendo programa e grafo
  -- putStrLn "\nDigite seu programa: "
  -- inputProgram <- getLine
  -- let pdlProgram = words inputProgram
  -- let programAST = parsePDL pdlProgram

  -- putStrLn "\nDigite cada aresta do grafo com seus elementos separados por espaço e aperte enter."
  -- putStrLn "Exemplo: a entrada 's1 s2 a' representa a aresta '(s1, s2, a)'."
  -- putStrLn "Para encerrar a inserção de arestas, digite 0."

  -- graph <- readGraph []
  -- print graph
  -- print (evaluateProgram programAST graph)