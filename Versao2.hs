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

--lendo o grafo, descomentar na main
readGraph :: Graph -> IO Graph
readGraph lines = do
    line <- getLine
    if line == "0"
        then return lines
    else do 
        let [fromState, toState, labelEdge] = words line
        readGraph((fromState, toState, labelEdge) : lines)

--pegando todas as arestas que contêm o atômico de entrada
getEdges :: Graph -> AtomicProgram -> [Edge]
getEdges graph labelEdge = 
    [(fromState, toState) | (fromState, toState, atomic) <- graph, atomic == labelEdge]

--pegando arestas transitivas para a avaliação da sequência
getTransitiveEdges :: [Edge] -> [Edge] -> [Edge]
getTransitiveEdges edges1 edges2 =
    [(fromState1, toState2) | (fromState1, toState1) <- edges1, (fromState2, toState2) <- edges2, toState1 == fromState2]

--pega as relações transitivas mais longas e independentes
--para a entrada [("1", "2"), ("2", "3"), ("3", "4"), ("4", "5"), ("5", "6"), ("6", "90"), ("7", "8"), ("8", "9"), ("9", "10"), ("10", "11"), ("11", "12"), ("23", "34"), ("34", "85")]
--a saída é [("1","90"),("7","12"),("23","85")]
getMaxTransitives :: [Edge] -> [Edge] -> [Edge]
getMaxTransitives [] outEdges = outEdges  -- Se a lista de arestas estiver vazia, retorna as arestas de saída acumuladas
getMaxTransitives edges outEdges =
    let ((fromState, toState), updatedEdges) = getMaxTransitive (head edges) (tail edges)
        -- Obtém a primeira aresta e a lista de arestas atualizada usando a função getMaxTransitive
    in getMaxTransitives updatedEdges (outEdges ++ [(fromState, toState)])
        -- Chama recursivamente com a lista atualizada de arestas e as arestas de saída acumuladas

getToState :: [Edge] -> (String, String)
getToState [] = ("", "")
getToState validEdges = (toState, finalState)
    where (toState, finalState) = head validEdges

getMaxTransitive :: Edge -> [Edge] -> (Edge, [Edge])
getMaxTransitive edge edges =
    let (fromState1, toState1) = edge
        -- Filtra as arestas com estado inicial igual ao estado de destino da aresta fornecida
        validEdges = getTransitiveEdges [edge] edges
        -- Obtém o estado inicial e o estado final da primeira aresta filtrada
        (fromState2, toState2) = getToState validEdges

        updatedEdges = filter (\(initialState, _) -> initialState /= toState1) edges
    in
        if fromState2 == ""
          -- Retorna a aresta fornecida e a lista original de arestas se não houver estado de destino válido
          then (edge, edges)  
          -- Chama recursivamente com os estados de origem e destino atualizados e a lista de arestas atualizada
          else getMaxTransitive (fromState1, toState2) updatedEdges
            

--funciona separadamente, mas na mensagem n vai por algum motivo
removeBackSlash :: [Char] -> [Char]
removeBackSlash string = [c | c <- string, c /= '\\']

evaluateProgram :: PDLProgram -> Graph -> (Bool, [Edge], String)
--caso atômico retorna todas as arestas que contem o programa como rótulo
evaluateProgram (AtomicProgram program) graph = 
    let edges = getEdges graph program
        sucessMessage = removeBackSlash ("Sucesso na avaliacao atomica do programa" ++ show program ++ ".")
        failMessage = removeBackSlash ("Falha na avaliacao atomica do programa" ++ show program ++ ".")
    in if edges /= []
        then (True, edges, sucessMessage)
        else (False, edges, failMessage)
evaluateProgram (OperatorProgram op [prog1, prog2]) graph = 
  case op of
      "U" -> evaluateNonDeterminism prog1 prog2 graph
      ";" -> evaluateSequence prog1 prog2 graph
evaluateProgram (OperatorProgram op [prog]) graph = 
  if op == "*" 
    then evaluateIteration prog graph
        else error "Invalid operator"

evaluateNonDeterminism :: PDLProgram -> PDLProgram -> Graph -> (Bool, [Edge], String)
evaluateNonDeterminism prog1 prog2 graph =
    let (result1, edges1, message1) = evaluateProgram prog1 graph 
    --curto circuito, o primeiro basta
    in if result1
      then (result1, edges1, message1)
    else evaluateProgram prog2 graph

evaluateSequence :: PDLProgram -> PDLProgram -> Graph -> (Bool, [Edge], String)
evaluateSequence prog1 prog2 graph = 
    let (result1, edges1, message1) = evaluateProgram prog1 graph 
        (result2, edges2, message2) = evaluateProgram prog2 graph
        sucessMessage = removeBackSlash "Sucesso na avaliacao sequencial do programa" ++ show prog1 ++ show prog2 ++ "."
        failMessage = removeBackSlash "Falha na avaliacao sequencial do programa" ++ show prog1 ++ show prog2 ++ "."
    --lado do prog1 vazio, mas verdadeiro devido à iteração
    in if result1 &&  edges1 == []
      -- pega o resultado do prog 2
      then (result2, edges2, sucessMessage)

    --lado do prog2 vazio, mas verdadeiro devido à iteração
    else if result2 &&  edges2 == []
      -- pega o resultado do prog 1 
      then (result1, edges1, sucessMessage)

    --ambos programas retornaram algo
    else 
        --extrair conjunto de edges em que o estado final do prog1 casa com o estado inicial do prog2 
        let transitiveEdges = getTransitiveEdges edges1 edges2
        in if result1 && result2 && transitiveEdges /= []
          -- ha pelo menos um no conjunto
          then (True, transitiveEdges, sucessMessage)
        -- esse conjunto é vazio
        else (False, transitiveEdges, failMessage)

evaluateIteration :: PDLProgram -> Graph -> (Bool, [Edge], String)
evaluateIteration prog graph =
    let (result, edges, message) =  evaluateProgram prog graph
        sucessMessage = removeBackSlash "Sucesso na evaliacao iterativa do programa" ++ show prog ++ "."
    --a iteração retorna sempre true, mas o segundo parâmetro pode ser vazio se a iteração não ocorrer
    in (True, getMaxTransitives edges [], sucessMessage)

main = do
    -- let teste1 = [("1", "2"), ("2", "3"), ("3", "4"), ("4", "5"), ("5", "6"), ("6", "90"), ("7", "8"), ("8", "9"), ("9", "10"), ("10", "11"), ("11", "12"), ("23", "34"), ("34", "85")]
    -- print (getMaxTransitives teste1 [])

    let pdlProgram1 = words "; U ; a b c * d"
    let programAST1 = parsePDL pdlProgram1


    let graph1_prog1 = [("s1", "s2", "c")]
    let graph2_prog1 = [("s1", "s2", "a"), ("s2", "s3", "b")]
    let graph3_prog1 = [("s1", "s2", "a"), ("s2", "s3", "b"), ("s3", "s4", "d"), ("s4", "s5", "k")]
    let graph4_prog1 = [("s1", "s2", "c"), ("s2", "s3", "d"), ("s3", "s4", "p")]
    let graph5_prog1 = [("s1", "s2", "a"), ("s2", "s3", "b"), ("s3", "s4", "k"), ("s4", "s5", "d")]
    let graph6_prog1 = [("s1", "s2", "a"), ("s2", "s3", "b"), ("s3", "s4", "k")]

    putStrLn "Resultado do Programa 1:"
    putStrLn ("O resultado do caso 1 é: " ++ show (evaluateProgram programAST1 graph1_prog1))
    putStrLn ("O resultado do caso 2 é: " ++ show (evaluateProgram programAST1 graph2_prog1))
    putStrLn ("O resultado do caso 3 é: " ++ show (evaluateProgram programAST1 graph3_prog1))
    putStrLn ("O resultado do caso 4 é: " ++ show (evaluateProgram programAST1 graph4_prog1))
    putStrLn ("O resultado do caso 5 é: " ++ show (evaluateProgram programAST1 graph5_prog1))
    putStrLn ("O resultado do caso 6 é: " ++ show (evaluateProgram programAST1 graph6_prog1))
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

  ---------------------------------------------------------------------------------------------

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