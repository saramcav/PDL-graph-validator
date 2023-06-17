module Versao3 where

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
parsePDLProgram ("?" : rest) =
  let (prog, rest1) = parsePDLProgram rest
  in (OperatorProgram "?" [prog], rest1)
parsePDLProgram (token : rest) = (AtomicProgram token, rest)
parsePDLProgram [] = error "Empty program"

pdlToString :: PDLProgram -> String
pdlToString (OperatorProgram op [prog1, prog2]) = op ++ " " ++ pdlToString prog1 ++ " " ++ pdlToString prog2
pdlToString (OperatorProgram op [prog]) = op ++ " " ++ pdlToString prog
pdlToString (AtomicProgram token) = token ++ " "

parsePDL :: [String] -> PDLProgram
parsePDL tokens =
  let (program, remainingTokens) = parsePDLProgram tokens
  in if null remainingTokens
      then program
      else error "Invalid program: Extra tokens remaining"

readGraph :: Graph -> IO Graph
readGraph lines = do
    line <- getLine
    if line == "0"
        then return lines
    else do 
        let [fromState, toState, labelEdge] = words line
        readGraph((fromState, toState, labelEdge) : lines)

getEdges :: Graph -> AtomicProgram -> [Edge]
getEdges graph labelEdge = 
    [(fromState, toState) | (fromState, toState, atomic) <- graph, atomic == labelEdge]

joinTransitiveEdges :: [Edge] -> [Edge] -> [Edge]
joinTransitiveEdges edges1 edges2 = [(fromState1, toState2) | (fromState1, toState1) <- edges1, 
                                                              (fromState2, toState2) <- edges2, 
                                                               toState1 == fromState2]

removeDuplicateEdges :: [Edge] -> [Edge]
removeDuplicateEdges edges = [edge | i <- [0 .. length edges - 1], let edge = edges !! i, edge `notElem` take i edges]

differenceEdges :: [Edge] -> [Edge] -> [Edge]
differenceEdges edges1 edges2 = [x | x <- edges1, x `notElem` edges2]

removeEdge :: Edge -> [Edge] -> [Edge]
removeEdge edge edges = [e | e <- edges, e /= edge]

isHeadEdge :: [Edge] -> [Edge] -> Bool
isHeadEdge edge edges = 
    let previousEdges = [toState2 | (fromState1, toState1) <- edge, 
                                    (fromState2, toState2) <- edges,    
                                    toState2 == fromState1]
    in (previousEdges == [])

getTransitiveEdges :: [Edge] -> [Edge] -> [Edge]
getTransitiveEdges edge edges = [(fromState2, toState2) | (fromState1, toState1) <- edge, 
                                                          (fromState2, toState2) <- edges, 
                                                          toState1 == fromState2]

getAllReflexiveEdges :: [Edge] -> [Edge]
getAllReflexiveEdges edges = [(fromState, toState) | (fromState, toState) <- edges, 
                                                      fromState == toState] 


getGraphReflexivePossibilities :: Graph -> [Edge]
getGraphReflexivePossibilities graph =
  let reflexives1 = [(fromState, fromState) | (fromState, toState, labelEdge) <- graph]
      reflexives2 = [(toState, toState) | (fromState, toState, labelEdge) <- graph]
   in removeDuplicateEdges (reflexives1 ++ reflexives2)

existsTransitive :: [Edge] -> [Edge] -> Bool
existsTransitive edge edges =
    let transitiveEdges = getTransitiveEdges edge edges 
         in (transitiveEdges /= [])

getAllHeadEdges :: [Edge] -> [Edge]
getAllHeadEdges edges = 
    [(fromState, toState) | (fromState, toState) <- edges, 
                            isHeadEdge [(fromState, toState)] edges]

getTransitivePossibilities :: [Edge] -> [Edge] -> [Edge]
getTransitivePossibilities [] edges2 = edges2
getTransitivePossibilities edges1 edges2 = 
    let reflexiveEdges = getAllReflexiveEdges edges1
    in if reflexiveEdges /= []
        then getHeadPossibleTransitive (differenceEdges edges1 reflexiveEdges) edges2
    else
        let headEdgesSet = getAllHeadEdges edges1
            headAllHeadEdges = head (headEdgesSet)
            possibleEdges = getHeadPossibleTransitive [headAllHeadEdges] edges1
            edges1' = removeEdge headAllHeadEdges edges1
            edges2' = removeDuplicateEdges edges2 ++ possibleEdges
        in getTransitivePossibilities edges1' edges2'

getHeadPossibleTransitive :: [Edge] -> [Edge] -> [Edge]
getHeadPossibleTransitive edge edges =
    if not (existsTransitive edge edges)
        then []
    else 
        let joinedTransitiveEdges = joinTransitiveEdges edge edges
            possibleTransitiveEdges = headCalls joinedTransitiveEdges edges
        in removeDuplicateEdges joinedTransitiveEdges ++ possibleTransitiveEdges

headCalls:: [Edge] -> [Edge] -> [Edge]
headCalls [] edges = []
headCalls edge edges =
    let currentEdge = head (edge)
        possibleEdges = getHeadPossibleTransitive [currentEdge] edges
        newEdge = removeEdge currentEdge edge
        possibleEdges' = headCalls newEdge edges 
    in removeDuplicateEdges possibleEdges ++ possibleEdges'


evaluateProgram :: PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateProgram (AtomicProgram prog) graph = evaluateAtomic prog graph
evaluateProgram (OperatorProgram op [prog1, prog2]) graph = 
  case op of
      "U" -> evaluateNonDeterminism prog1 prog2 graph
      ";" -> evaluateSequence prog1 prog2 graph
evaluateProgram (OperatorProgram op [prog]) graph = 
  case op of
      "*" -> evaluateIteration prog graph
      "?" -> evaluateTest prog graph
      otherwise -> error "Invalid operator"

evaluateAtomic :: String -> Graph -> (Bool, [Edge], [String])
evaluateAtomic prog graph = 
    let edges = getEdges graph prog
        successMessage = "Sucesso na avaliacao atomica do programa >>> " ++ prog
        failMessage = "Falha na avaliacao atomica do programa >>> " ++ prog
    in if edges /= []
        then (True, edges, [""])
        else (False, edges,[""])

evaluateNonDeterminism :: PDLProgram -> PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateNonDeterminism prog1 prog2 graph =
    let (result1, edges1, message1) = evaluateProgram prog1 graph 
        (result2, edges2, message2) = evaluateProgram prog2 graph
        successMessage = "Sucesso na avaliacao nao deterministica do programa >>> " ++ pdlToString prog1 ++ pdlToString prog2
        failMessage = "Falha na avaliacao nao deterministica do programa >>> " ++ pdlToString prog1 ++ pdlToString prog2
        finalMessage = message1 ++ message2 ++ [successMessage]
    in if result1 || result2
        then(True, edges1 ++ edges2, [""])
    else (False, edges1 ++ edges2, [""])
    -- aqui nao pode fazer curto circuito pq se o programa (a;(b U c)) fosse testado com o grafo:
    -- (1)---a--->(2)---c--->(3)---b--->(4) retornaria false já que b já retornaria [(3,4)] para a avaliacao sequencial
    -- entao a avaliacao sequencial pegaria [(1, 2)] de a, que não é considerado transitivo à b

evaluateSequence :: PDLProgram -> PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateSequence prog1 prog2 graph = 
    let (result1, edges1, message1) = evaluateProgram prog1 graph 
        (result2, edges2, message2) = evaluateProgram prog2 graph
        successMessage = "Sucesso na avaliacao sequencial do programa >>> " ++ pdlToString prog1 ++ pdlToString prog2
        failMessage = "Falha na avaliacao sequencial do programa >>> " ++ pdlToString prog1 ++ pdlToString prog2
        finalMessage = message1 ++ message2 ++ [successMessage]
        joinedTransitiveEdges = joinTransitiveEdges edges1 edges2
    in if result1 && result2 && joinedTransitiveEdges /= []
        then (True, joinedTransitiveEdges, [""])
    else (False, joinedTransitiveEdges, [""])

evaluateIteration :: PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateIteration program graph =
    let (result, edges, message) =  evaluateProgram program graph
        --fazendo a uniao
        reflexiveElements = getGraphReflexivePossibilities graph
        transitivePossibilities = getTransitivePossibilities edges []
        iterationPossibilitiesSet = edges ++ transitivePossibilities ++ reflexiveElements
    in (True, removeDuplicateEdges iterationPossibilitiesSet, [""])

evaluateTest :: PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateTest program graph =
    let (result, edges, message) =  evaluateProgram program graph
        --fazendo a uniao
        reflexiveElements = getGraphReflexivePossibilities graph
    in (True, removeDuplicateEdges reflexiveElements, [""])

getMessages :: (a, b, c) -> c
getMessages (_, _, x) = x

main = do
    let teste = [("1", "2"), ("2", "3"), ("3", "4"), ("2", "5"), ("7", "8")]
    putStrLn("Aqui a saida desse caso de exemplo para pegar as possibilidades transitivas:")
    print(getTransitivePossibilities teste [])
    putStrLn "\n\n"

    let pdlProgram1 = words "; U ; a b c * d"
    let programAST1 = parsePDL pdlProgram1


    let graph1_prog1 = [("s1", "s2", "c")]
    let graph2_prog1 = [("s1", "s2", "a"), ("s2", "s3", "b")]
    let graph3_prog1 = [("s1", "s2", "a"), ("s2", "s3", "b"), ("s3", "s4", "d"), ("s4", "s5", "k")]
    let graph4_prog1 = [("s1", "s2", "c"), ("s2", "s3", "d"), ("s3", "s4", "p")]
    let graph5_prog1 = [("s1", "s2", "a"), ("s2", "s3", "b"), ("s3", "s4", "k"), ("s4", "s5", "d")]
    let graph6_prog1 = [("s1", "s2", "a"), ("s2", "s3", "b"), ("s3", "s4", "k")]
    let graph7_prog1 = [("s3", "s1", "a"), ("s1", "s2", "b"), ("s2","s3","k"), ("s3","s4","d"), ("s4", "s2", "h")]
    let graph8_prog1 = [("s3", "s1", "d"), ("s1", "s2", "c"), ("s2","s3","k")]
    let graph9_prog1 = [("s3", "s1", "e"), ("s1", "s2", "f"), ("s2","s3","g")]

    putStrLn "Resultado do Programa 1:"
    putStrLn ("O resultado do caso 1 é: " ++ show (evaluateProgram programAST1 graph1_prog1))
    putStrLn ("O resultado do caso 2 é: " ++ show (evaluateProgram programAST1 graph2_prog1))
    putStrLn ("O resultado do caso 3 é: " ++ show (evaluateProgram programAST1 graph3_prog1))
    putStrLn ("O resultado do caso 4 é: " ++ show (evaluateProgram programAST1 graph4_prog1))
    putStrLn ("O resultado do caso 5 é: " ++ show (evaluateProgram programAST1 graph5_prog1))
    putStrLn ("O resultado do caso 6 é: " ++ show (evaluateProgram programAST1 graph6_prog1))
    putStrLn ("O resultado do caso 7 é: " ++ show (evaluateProgram programAST1 graph7_prog1))
    putStrLn ("O resultado do caso 8 é: " ++ show (evaluateProgram programAST1 graph8_prog1))
    putStrLn ("O resultado do caso 9 é: " ++ show (evaluateProgram programAST1 graph9_prog1))
    print (head (getMessages (evaluateProgram programAST1 graph9_prog1)))
    putStrLn "\n"

    ---------------------------------------------------------------------------------------------

    let pdlProgram2 = words "; * ; * U a b c d"
    let programAST2 = parsePDL pdlProgram2

    let graph1_prog2 = [("s1", "s2", "c"), ("s2", "s3", "d")]
    let graph2_prog2 = [("s1", "s2", "d")]
    let graph3_prog2 = [("s1", "s2", "a"), ("s2", "s3", "c"), ("s3", "s4", "d")]
    let graph4_prog2 = [("s1", "s2", "c"), ("s2", "s3", "k"), ("s3", "s4", "d")]
    let graph5_prog2 = [("s1", "s2", "d"), ("s2", "s3", "z")]

    putStrLn "Resultado do Programa 2:"
    putStrLn ("O resultado do caso 1 é: " ++ show (evaluateProgram programAST2 graph1_prog2))
    putStrLn ("O resultado do caso 2 é: " ++ show (evaluateProgram programAST2 graph2_prog2))
    putStrLn ("O resultado do caso 3 é: " ++ show (evaluateProgram programAST2 graph3_prog2))
    putStrLn ("O resultado do caso 4 é: " ++ show (evaluateProgram programAST2 graph4_prog2))
    putStrLn ("O resultado do caso 5 é: " ++ show (evaluateProgram programAST2 graph5_prog2))
    putStrLn "\n"

  ---------------------------------------------------------------------------------------------

    let pdlProgram3 = words "; a * d"
    let programAST3 = parsePDL pdlProgram3
    let graph1_prog3 = [("s1", "s2", "a")]
    let graph2_prog3 = [("s1", "s2", "a"), ("s2", "s3", "d")]
    let graph3_prog3 = [("s1", "s2", "a"), ("s2", "s3", "k"), ("s3", "s4", "d")]

    putStrLn "Resultado do Programa 3:"
    putStrLn ("O resultado do caso 1 é: " ++ show (evaluateProgram programAST3 graph1_prog3))
    putStrLn ("O resultado do caso 2 é: " ++ show (evaluateProgram programAST3 graph2_prog3))
    putStrLn ("O resultado do caso 3 é: " ++ show (evaluateProgram programAST3 graph3_prog3))
    putStrLn "\n"

    -------------------------------------------------------------------------------------------

    let pdlProgram4 = words "U a a"
    let programAST4 = parsePDL pdlProgram4
    let graph1_prog4 = [("s1", "s2", "a"), ("s2", "s1", "a")]
    
    putStrLn "Resultado do Programa 4:"
    putStrLn ("O resultado do caso 1 é: " ++ show (evaluateProgram programAST4 graph1_prog4))
    print (head (getMessages (evaluateProgram programAST4 graph1_prog4)))

    -------------------------------------------------------------------------------------------

    -- putStrLn "\n---------------------------------------------------------------------------------------------------"
    -- putStrLn "\nO programa deve ser escrito de forma prefixada e com espaço entre caracteres."
    -- putStrLn "Exemplo: \"; a * d\" representa \"a;(*d)\"\nDigite abaixo:"
    -- inputProgram <- getLine
    -- let pdlProgram = words inputProgram
    -- let programAST = parsePDL pdlProgram

    -- putStrLn "\nDigite abaixo cada aresta do grafo com seus elementos separados por espaço e aperte enter."
    -- putStrLn "Exemplo: a entrada 's1 s2 a' representa a aresta '(s1, s2, a)'."
    -- putStrLn "Para encerrar a inserção de arestas, digite 0."

    -- graph <- readGraph []
    -- print (evaluateProgram programAST graph)