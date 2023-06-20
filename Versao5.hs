module Versao5 where

import Data.List (nub)

type State = String
type AtomicProgram = String
type NamedEdge = (State, State, AtomicProgram)
type Edge = (State, State)
type Graph = [NamedEdge]

data PDLProgram = AtomicProgram String | 
                  OperatorProgram String [PDLProgram] 
                  deriving Show

-- avaliacao sintatica 

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
parsePDLProgram [] = error "ERRO SINTATICO: Programa vazio"

parsePDL :: [String] -> PDLProgram
parsePDL tokens =
  let (program, remainingTokens) = parsePDLProgram tokens
  in if null remainingTokens
      then program
      else error "ERRO SINTATICO: Programa inválido. Faltam símbolos."

--funcoes auxiliares de entrada 

readGraph :: Graph -> IO Graph
readGraph lines = do
    line <- getLine
    if line == "0"
        then return lines
    else do 
        let [fromState, toState, labelEdge] = words line
        readGraph((fromState, toState, labelEdge) : lines)

executeEntryLoop :: IO ()
executeEntryLoop = do
    putStrLn("\n\nEntrada--------------------------------------------------------------------------")
    putStrLn "\nO programa deve ser escrito de forma prefixada e com espaço entre caracteres."
    putStrLn "Exemplo: \"; a * d\" representa \"a;(*d)\"\nDigite abaixo:"
    inputProgram <- getLine
    let pdlProgram = words inputProgram
        programAST = parsePDL pdlProgram

    putStrLn "\nDigite abaixo cada aresta do grafo com seus elementos separados por espaço e aperte enter."
    putStrLn "Exemplo: a entrada 's1 s2 a' representa a aresta '(s1, s2, a)'."
    putStrLn "Para encerrar a inserção de arestas, digite 0."

    graph <- readGraph []
    evaluateAndPrint (programAST, graph)

    putStrLn "\nDeseja realizar uma nova avaliação? (sim/não)"
    answer <- getLine
    if answer `elem` ["sim", "s", "yes", "y", "S", "Y"]
        then executeEntryLoop
        else putStrLn "Encerrando o programa."

-- funcoes auxiliares de saida

pdlToString :: PDLProgram -> String
pdlToString (OperatorProgram op [prog1, prog2]) = op ++ " " ++ pdlToString prog1 ++ " " ++ pdlToString prog2
pdlToString (OperatorProgram op [prog]) = op ++ " " ++ pdlToString prog
pdlToString (AtomicProgram token) = token ++ " "

getFinalMessage :: (Bool, [Edge], [String]) -> String
getFinalMessage (result, _, _) = let success = "Sim, o conjunto de vértices e arestas rotuladas correspondem a um frame satisfazível para o programa."
                                     fail = "Não, o conjunto de vértices e arestas rotuladas não permitem um caminho pelo qual seja possível executar o programa."
                                 in if result then success
                                 else  fail 

printMessageList :: [String] -> IO ()
printMessageList []     = return ()  
printMessageList (message : messages) = do
    putStrLn message
    printMessageList messages


evaluateAndPrint :: (PDLProgram, Graph) -> IO ()
evaluateAndPrint (pdlProgram, graph) = do
    let evaluation = evaluateProgram pdlProgram graph
    let messages = getMessages evaluation
    putStrLn ("Resultado do Programa \"" ++ pdlToString pdlProgram ++  "\"\nPara o grafo: " ++ show graph ++ "\n")
    printMessageList messages
    putStrLn ("\nResultado final: " ++ getFinalMessage evaluation)

getMessages :: (Bool, [Edge], [String]) -> [String]
getMessages (_, _, messages) = messages

-- funcoes auxiliares para avaliacao semantica

getEdges :: Graph -> AtomicProgram -> [Edge]
getEdges graph labelEdge = 
    [(fromState, toState) | (fromState, toState, atomic) <- graph, atomic == labelEdge]

joinTransitiveEdges :: [Edge] -> [Edge] -> [Edge]
joinTransitiveEdges edges1 edges2 = [(fromState1, toState2) | (fromState1, toState1) <- edges1, 
                                                              (fromState2, toState2) <- edges2, 
                                                               toState1 == fromState2]

getGraphReflexivePossibilities :: Graph -> [Edge]
getGraphReflexivePossibilities graph =
    let reflexives1 = [(fromState, fromState) | (fromState, toState, labelEdge) <- graph]
        reflexives2 = [(toState, toState) | (fromState, toState, labelEdge) <- graph]
    in nub (reflexives1 ++ reflexives2)

-- Retorna todas as transitivas internas entre duas listas de estados
-- ou seja, para a entrada [("1", "2"), ("2", "3"), ("3", "4"), ("2", "5"), ("7", "8"), ("8", "9")]
-- o retorno seria [("1", "3"), ("1", "4"), ("2", "4"), ("1", "5"), ("7", "9")]
-- removendo reflexivas e já existentes no input
getTransitivePossibilities :: [Edge] -> [Edge] -> [Edge]
getTransitivePossibilities edges1 edges2 =
  let allStates = nub $ concatMap (\(from, to) -> [from, to]) (edges1 ++ edges2)
      transitiveStates = [(from, to) | from <- allStates, to <- allStates, reachable from to []]
  in filter (\(from, to) -> (from, to) `notElem` (edges1 ++ edges2) && from /= to) transitiveStates
  where
    reachable :: State -> State -> [State] -> Bool
    reachable from to visited
      | from == to = True
      | from `elem` visited = False  -- Avoid revisiting already visited states
      | otherwise = any (\(_, next) -> reachable next to (from : visited)) (filter (\(start, _) -> start == from) edges1)
                   || any (\(_, next) -> reachable next to (from : visited)) (filter (\(start, _) -> start == from) edges2)

-- avaliacao semantica
-- o segundo elemento da tupla representa as relacoes pelas quais se e possivel "passar"
-- as mensagens de erro de cada avaliacao sao inseridas na lista de mensagens, que esta no ultimo elemento da tupla de saida
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
      otherwise -> error "Operador inválido"

evaluateAtomic :: String -> Graph -> (Bool, [Edge], [String])
evaluateAtomic prog graph = 
    -- pega as ocorrencias (a,b) de uma label atomica de aresta
    let edges = getEdges graph prog
        successMessage = "Sucesso na avaliação atômica do operando (" ++ prog ++ ") -> " ++ show edges
        failMessage = "Falha na avaliação atômica do operando (" ++ prog ++ ")"
    in if edges /= []
        then (True, edges, [successMessage])
        else (False, edges,[failMessage])

evaluateNonDeterminism :: PDLProgram -> PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateNonDeterminism prog1 prog2 graph =
    let (result1, edges1, message1) = evaluateProgram prog1 graph 
        (result2, edges2, message2) = evaluateProgram prog2 graph
        outputEdges = nub (edges1 ++ edges2)
        successMessage = "Sucesso na avaliação não determinística dos operandos  (" ++ pdlToString prog1 ++ ") e (" ++ pdlToString prog2 ++ ") -> " ++  show outputEdges
        failMessage = "Falha na avaliação não determinística dos operandos (" ++ pdlToString prog1 ++ ") e (" ++ pdlToString prog2 ++ ")"
        finalSuccessMessage = message1 ++ message2 ++ [successMessage]
        finalFailMessage = message1 ++ message2 ++ [failMessage]
        
    in if result1 || result2
        then(True, outputEdges, finalSuccessMessage)
    else (False, outputEdges, finalFailMessage)
    -- aqui nao pode fazer curto circuito pq se o programa (a;(b U c)) fosse testado com o grafo:
    -- (1)---a--->(2)---c--->(3)---b--->(4) retornaria falso já que b já retornaria [(3,4)] para a avaliacao sequencial
    -- entao a avaliacao sequencial pegaria [(1, 2)] de a, que não seria considerado transitivo a b

evaluateSequence :: PDLProgram -> PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateSequence prog1 prog2 graph = 
    let (result1, edges1, message1) = evaluateProgram prog1 graph 
        (result2, edges2, message2) = evaluateProgram prog2 graph
        -- Poderiamos fazer curto circuito aqui, evitando uma linha de avaliação no segundo programa, mas para
        -- preservar o histórico de falhas de avaliação por completo optamos por não o fazer
        joinedTransitiveEdges = joinTransitiveEdges edges1 edges2

        successMessage = "Sucesso na avaliação sequencial dos operandos (" ++ pdlToString prog1 ++ ") e (" ++ pdlToString prog2 ++ ") -> " ++ show joinedTransitiveEdges
        failMessage = "Falha na avaliação sequencial dos operandos  (" ++ pdlToString prog1 ++ ") e (" ++ pdlToString prog2 ++ ")"
        
        finalSuccessMessage = message1 ++ message2 ++ [successMessage]
        finalFailMessage = message1 ++ message2 ++ [failMessage]

    in if result1 && result2 && joinedTransitiveEdges /= []
        then (True, joinedTransitiveEdges, finalSuccessMessage)
    else (False, joinedTransitiveEdges, finalFailMessage)

evaluateIteration :: PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateIteration program graph =
    let (result, edges, message) =  evaluateProgram program graph

        reflexiveElements = getGraphReflexivePossibilities graph
        transitivePossibilities = getTransitivePossibilities edges []
        iterationPossibilitiesSet = edges ++ transitivePossibilities ++ reflexiveElements

        successMessage = "Sucesso na avaliação iterativa do operando (" ++ pdlToString program ++ ") -> " ++  show iterationPossibilitiesSet

    in (True, nub iterationPossibilitiesSet, [successMessage])

evaluateTest :: PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateTest program graph = 
    let (result, edges, message) =  evaluateProgram program graph
        iterationMessage = "Teste de (" ++ pdlToString program ++ ") ignorado pela avaliação."
        reflexiveElements = getGraphReflexivePossibilities graph
    in (True, reflexiveElements, [iterationMessage])

main = do
    -- esses casos de teste estao desenhados no arquivo "casos_de_teste.txt"
    putStrLn("\n\nPrograma 1--------------------------------------------------------------------------")
    let pdlProgram1 = words "; U ; a b c * d"
    let programAST1 = parsePDL pdlProgram1
    let graph1_prog1 = [("s3", "s1", "a"), ("s1", "s2", "b"), ("s2","s3","k"), ("s3","s4","d"), ("s4", "s2", "h")]
    let graph2_prog1 = [("s3", "s1", "d"), ("s1", "s2", "c"), ("s2","s3","k")]
    let graph3_prog1 = [("s3", "s1", "e"), ("s1", "s2", "f"), ("s2","s3","g")]
    putStrLn("\n--------Caso 1")
    evaluateAndPrint (programAST1, graph1_prog1)
    putStrLn("\n--------Caso 2")
    evaluateAndPrint (programAST1, graph2_prog1)
    putStrLn("\n--------Caso 3")
    evaluateAndPrint (programAST1, graph3_prog1)

    putStrLn("\n\nPrograma 2--------------------------------------------------------------------------")
    let pdlProgram2 = words "; * ; * U a b c d"
    let programAST2 = parsePDL pdlProgram2
    let graph1_prog2 = [("s1", "s2", "a"), ("s2", "s3", "c"), ("s3", "s4", "d")]
    let graph2_prog2 = [("s1", "s2", "c"), ("s2", "s3", "k"), ("s3", "s4", "d")]
    putStrLn("\n--------Caso 1")
    evaluateAndPrint (programAST2, graph1_prog2)
    putStrLn("\n--------Caso 2")
    evaluateAndPrint (programAST2, graph2_prog2)

    putStrLn("\n\nPrograma 3--------------------------------------------------------------------------")
    let pdlProgram3 = words "; ? c U * k * a"
    let programAST3 = parsePDL pdlProgram3
    let graph1_prog3 = [("s1", "s2", "a"), ("s2", "s3", "c"), ("s3", "s4", "b")]
    putStrLn("\n--------Caso 1")
    evaluateAndPrint (programAST3, graph1_prog3)

    putStrLn("\n\nPrograma 4--------------------------------------------------------------------------")
    let pdlProgram4 = words "; a * ? d"
    let programAST4 = parsePDL pdlProgram4
    let graph1_prog4 = [("s1", "s2", "a"), ("s2", "s3", "d"), ("s3", "s2", "d")]
    putStrLn("\n--------Caso 1")
    evaluateAndPrint (programAST4, graph1_prog4)

    putStrLn("\n\nPrograma 5--------------------------------------------------------------------------")
    let pdlProgram5 = words "; k ; * a ; a ; a b"
    let programAST5 = parsePDL pdlProgram5
    let graph1_prog5 = [("s0", "s1", "k"),("s1", "s2", "a"), ("s2", "s3", "a"), ("s3", "s1", "a"), ("s2", "s5", "b")]
    putStrLn("\n--------Caso 1")
    evaluateAndPrint (programAST5, graph1_prog5)

    executeEntryLoop