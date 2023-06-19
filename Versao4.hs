module Versao4 where

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
parsePDLProgram [] = error "Programa vazio"

parsePDL :: [String] -> PDLProgram
parsePDL tokens =
  let (program, remainingTokens) = parsePDLProgram tokens
  in if null remainingTokens
      then program
      else error "Programa inválido. Faltam símbolos."

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
    putStrLn("\n\nEntrada-------------------------------------------------------------------------------------------------------------------------------")
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
    if answer == "sim"
        then executeEntryLoop
        else putStrLn "Encerrando o programa."

-- funcoes auxiliares de saida

pdlToString :: PDLProgram -> String
pdlToString (OperatorProgram op [prog1, prog2]) = op ++ " " ++ pdlToString prog1 ++ " " ++ pdlToString prog2
pdlToString (OperatorProgram op [prog]) = op ++ " " ++ pdlToString prog
pdlToString (AtomicProgram token) = token ++ " "

getMessages :: (Bool, [Edge], [String]) -> [String]
getMessages (_, _, messages) = messages

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
    putStrLn ("Resultado do Programa \"" ++ pdlToString pdlProgram ++  "\" com o grafo " ++ show graph ++ ":")
    printMessageList messages
    putStrLn ("Resultado final: " ++ getFinalMessage evaluation)

-- funcoes auxiliares para avaliacao semantica

getEdges :: Graph -> AtomicProgram -> [Edge]
getEdges graph labelEdge = 
    [(fromState, toState) | (fromState, toState, atomic) <- graph, atomic == labelEdge]

joinTransitiveEdges :: [Edge] -> [Edge] -> [Edge]
joinTransitiveEdges edges1 edges2 = [(fromState1, toState2) | (fromState1, toState1) <- edges1, 
                                                              (fromState2, toState2) <- edges2, 
                                                               toState1 == fromState2]

removeDuplicateEdges :: [Edge] -> [Edge]
removeDuplicateEdges edges = [edge | i <- [0 .. length edges - 1], 
                                          let edge = edges !! i, 
                                          edge `notElem` take i edges]

differenceEdges :: [Edge] -> [Edge] -> [Edge]
differenceEdges edges1 edges2 = [edge | edge <- edges1, edge `notElem` edges2]

removeEdge :: Edge -> [Edge] -> [Edge]
removeEdge edge edges = [edge | edge <- edges, edge /= edge]

isHeadEdge :: [Edge] -> [Edge] -> Bool
isHeadEdge edge edges = 
    let previousEdges = [toState2 | (fromState1, toState1) <- edge, 
                                    (fromState2, toState2) <- edges,    
                                    toState2 == fromState1]
    in (previousEdges == [])

-- pega todas as arestas (a, b) para as quais não existe aresta do tipo (_, a)
getAllHeadEdges :: [Edge] -> [Edge]
getAllHeadEdges edges = [(fromState, toState) | (fromState, toState) <- edges, 
                                                isHeadEdge [(fromState, toState)] edges]  

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

-- o objetivo de getTransitivePossibilities e retornar todos os "caminhos" possiveis entre os filhos da iteracao
-- ou seja, para a entrada [("1", "2"), ("2", "3"), ("3", "4"), ("2", "5"), ("7", "8"), ("8", "9")]
-- o retorno seria [("1", "3"), ("1", "4"), ("2", "4"), ("1", "5"), ("7", "9")]
-- ela chama getHeadPossibleTransitive para todas "arestas cabeca", que nesse exemplo seriam ("1", "2") e ("7", "8")
-- pois nao existem arestas do tipo (_, "1") nem (_, "7") na entrada
getTransitivePossibilities :: [Edge] -> [Edge] -> [Edge]
getTransitivePossibilities [] edges2 = edges2
getTransitivePossibilities edges1 edges2 = 
    let reflexiveEdges = getAllReflexiveEdges edges1
    in if reflexiveEdges /= []
        then getHeadPossibleTransitive (differenceEdges edges1 reflexiveEdges) edges2
    else
        let headEdgesSet = getAllHeadEdges edges1
        in if headEdgesSet /= []
            then
                let headAllHeadEdges = head (headEdgesSet)
                    possibleEdges = getHeadPossibleTransitive [headAllHeadEdges] edges1
                    edges1' = removeEdge headAllHeadEdges edges1
                    edges2' = removeDuplicateEdges edges2 ++ possibleEdges
                in getTransitivePossibilities edges1' edges2'
            else
                []

-- pega o caminho maximo possivel e todos os intermediarios dentro dele para cada "aresta cabeca"
-- [("1", "3"), ("1", "4"), ("2", "4"), ("1", "5")] para ("1", "2")
-- [("7", "9") para ("7", "8")]
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
        successMessage = "Sucesso na avaliação atômica do operando (" ++ prog ++ ") \26 " ++ show edges
        failMessage = "Falha na avaliação atômica do operando (" ++ prog ++ ")"
    in if edges /= []
        then (True, edges, [successMessage])
        else (False, edges,[failMessage])

evaluateNonDeterminism :: PDLProgram -> PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateNonDeterminism prog1 prog2 graph =
    let (result1, edges1, message1) = evaluateProgram prog1 graph 
        (result2, edges2, message2) = evaluateProgram prog2 graph
        outputEdges = removeDuplicateEdges (edges1 ++ edges2)
        successMessage = "Sucesso na avaliação não determinística dos operandos  (" ++ pdlToString prog1 ++ ") e (" ++ pdlToString prog2 ++ ") \26 " ++  show outputEdges
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
        -- a funcao joinTransitiveEdges pega arestas (a,b) e (b,c) e forma arestas (a,c)
        joinedTransitiveEdges = joinTransitiveEdges edges1 edges2
        successMessage = "Sucesso na avaliação sequencial dos operandos (" ++ pdlToString prog1 ++ ") e (" ++ pdlToString prog2 ++ ") \26 " ++ show joinedTransitiveEdges
        failMessage = "Falha na avaliação sequencial dos operandos  (" ++ pdlToString prog1 ++ ") e (" ++ pdlToString prog2 ++ ")"
        finalSuccessMessage = message1 ++ message2 ++ [successMessage]
        finalFailMessage = message1 ++ message2 ++ [failMessage]

    in if result1 && result2 && joinedTransitiveEdges /= []
        then (True, joinedTransitiveEdges, finalSuccessMessage)
    else (False, joinedTransitiveEdges, finalFailMessage)

evaluateIteration :: PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateIteration program graph =
    let (result, edges, message) =  evaluateProgram program graph
        --fazendo a uniao
        reflexiveElements = getGraphReflexivePossibilities graph
        transitivePossibilities = getTransitivePossibilities edges []
        iterationPossibilitiesSet = edges ++ transitivePossibilities ++ reflexiveElements
        successMessage = "Sucesso na avaliação iterativa do operando (" ++ pdlToString program ++ ") \26 " ++  show iterationPossibilitiesSet
    in (True, removeDuplicateEdges iterationPossibilitiesSet, [successMessage])

evaluateTest :: PDLProgram -> Graph -> (Bool, [Edge], [String])
evaluateTest program graph = 
    let (result, edges, message) =  evaluateProgram program graph
        iterationMessage = "Teste de (" ++ pdlToString program ++ ") ignorado pela avaliação."
        reflexiveElements = getGraphReflexivePossibilities graph
    in (True, reflexiveElements, [iterationMessage])

main = do
    -- esses casos de teste estao desenhados no arquivo "casos_de_teste.txt"
    putStrLn("\n\nPrograma 1-------------------------------------------------------------------------------------------------------------------------------")
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

    putStrLn("\n\nPrograma 2-------------------------------------------------------------------------------------------------------------------------------")
    let pdlProgram2 = words "; * ; * U a b c d"
    let programAST2 = parsePDL pdlProgram2
    let graph1_prog2 = [("s1", "s2", "a"), ("s2", "s3", "c"), ("s3", "s4", "d")]
    let graph2_prog2 = [("s1", "s2", "c"), ("s2", "s3", "k"), ("s3", "s4", "d")]
    putStrLn("\n--------Caso 1")
    evaluateAndPrint (programAST2, graph1_prog2)
    putStrLn("\n--------Caso 2")
    evaluateAndPrint (programAST2, graph2_prog2)

    putStrLn("\n\nPrograma 3-------------------------------------------------------------------------------------------------------------------------------")
    let pdlProgram3 = words "; ? c U * k * a"
    let programAST3 = parsePDL pdlProgram3
    let graph1_prog3 = [("s1", "s2", "a"), ("s2", "s3", "c"), ("s3", "s4", "b")]
    putStrLn("\n--------Caso 1")
    evaluateAndPrint (programAST3, graph1_prog3)

    putStrLn("\n\nPrograma 4-------------------------------------------------------------------------------------------------------------------------------")
    let pdlProgram4 = words "; a * d"
    let programAST4 = parsePDL pdlProgram4
    let graph1_prog4 = [("s1", "s2", "a"), ("s2", "s3", "d"), ("s3", "s2", "d")]
    putStrLn("\n--------Caso 1")
    evaluateAndPrint (programAST4, graph1_prog4)

    executeEntryLoop