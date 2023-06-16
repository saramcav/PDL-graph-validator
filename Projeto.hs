type State = String
type AtomicProgram = String
type NamedEdge = (State, State, AtomicProgram)
type Graph = [NamedEdge]

data PDLProgram = AtomicProgram String | OperatorProgram String [PDLProgram] deriving Show

-- Syntactic Evaluation

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


-- Semantic Evaluation

getInitialState :: Graph -> String
getInitialState [] = ""
getInitialState ((state, _, _):_) = state

startEvaluation :: PDLProgram -> Graph -> (Bool, State)
startEvaluation prog graph = 
  let state = getInitialState graph
  in evaluateProgram prog graph state

evaluateProgram :: PDLProgram -> Graph -> State -> (Bool, State)

evaluateProgram (AtomicProgram program) graph state =
  -- Busca pela aresta
  let matchingEdge = findMatchingEdge graph
  -- Repete estado anterior se não encontrar e considera falso
  -- Avança para o próximo estado caso encontre e considera verdadeiro
  in case matchingEdge of
    Nothing -> (False, state)
    Just (_, nextState, _) -> (True, nextState)
  where
    -- Dado o grafo (e acessando o programa / estado do escopo anterior) determina se a aresta atual é válida
    -- Se não, tenta com o resto das arestas até acabar o grafo e retornar nothing
    findMatchingEdge :: Graph -> Maybe NamedEdge
    findMatchingEdge [] = Nothing
    findMatchingEdge ((fromState, nextState, atomicProgram):rest)
      | atomicProgram == program && fromState == state = Just (fromState, nextState, atomicProgram)
      | otherwise = findMatchingEdge rest

evaluateProgram (OperatorProgram op children) graph state =
  case op of
    ";" -> evaluateSequence children graph state
    "U" -> evaluateOption children graph state
    "*" -> evaluateIteration (head children) graph state
    _ -> error "Invalid operator"

evaluateSequence :: [PDLProgram] -> Graph -> State -> (Bool, State)
evaluateSequence [] _ _ = (True, "")
evaluateSequence (prog1 : prog2 : rest) graph state =
  let (b1, state1) = evaluateProgram prog1 graph state
      -- Checa prog2 somente se prog1 é verdadeiro, senão pode retornar falso desde já apontando o estado falho
      (b2, state2) = if b1 then evaluateProgram prog2 graph state1 else (False, state) 
  in (b2, state2)

evaluateOption :: [PDLProgram] -> Graph -> State -> (Bool, State)
evaluateOption (prog1 : prog2 : rest) graph state =
  let (b1, state1) = evaluateProgram prog1 graph state
      (b2, state2) = evaluateProgram prog2 graph state
      nState = if b1 then state1 else if b2 then state2 else state
      b = b1 || b2
  in (b, nState)

--TODO: Test this function
evaluateIteration :: PDLProgram -> Graph -> State -> (Bool, State)
evaluateIteration prog graph state =
  let (isValid, finalState) = checkIteration prog graph state
  in (isValid, finalState)


checkIteration :: PDLProgram -> Graph -> State -> (Bool, State)
checkIteration prog graph state =
  let (isValid, newState) = evaluateProgram prog graph state
  in if isValid
       then (True, newState)
       else case evaluateProgram (OperatorProgram "*" [prog]) graph state of
              (True, finalState) -> (True, finalState)
              _ -> (False, state)





main :: IO ()
main = do
  let pdlProgram = "; ; b * c d"
      programAST = parsePDL (words pdlProgram)
      graph = [("s3", "s4", "b"), ("s4", "s5", "c"), ("s5", "s6", "c"), ("s6", "s7", "d")]
      (isValid, endState) = startEvaluation programAST graph
  putStrLn $ "\nAvaliating program: " ++ show pdlProgram
  putStrLn $ "\nGraph:"
  mapM_ print graph

  putStrLn $ "\nIs graph valid for the program? " ++ show isValid
  putStrLn $ "End State: " ++ show endState
