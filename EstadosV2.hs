type State = String
type Program = String
type LabeledEdge = (State, State, Program)
type Graph = [LabeledEdge]

-- Function to check if a program can execute in the given graph
validProgram :: Program -> Graph -> Bool
validProgram program graph = any (\(fromState, _, _) -> validPath program graph fromState []) graph

-- Helper function to check if a path matches a program
validPath :: Program -> Graph -> State -> [State] -> Bool
validPath "" _ _ _ = True -- An empty program matches any path
validPath (p:ps) graph currentState visitedStates
  | p == '*' = validIteration ps graph currentState visitedStates
  | p == ';' = validSequence ps graph currentState visitedStates
  | p == 'U' = validChoice ps graph currentState visitedStates
  | otherwise = validAtomicProgram p ps graph currentState visitedStates

-- Helper function to check if an atomic program matches a path
validAtomicProgram :: Char -> Program -> Graph -> State -> [State] -> Bool
validAtomicProgram atomicProgram restProgram graph currentState visitedStates =
  case findMatchingEdges currentState atomicProgram graph of
    [] -> False -- No matching edge found
    matchingEdges ->
      any (\(_, toState, _) -> validPath restProgram graph toState (toState:visitedStates)) matchingEdges

-- Helper function to check if a sequence of programs matches a path
validSequence :: Program -> Graph -> State -> [State] -> Bool
validSequence restProgram graph currentState visitedStates =
  case findMatchingEdges currentState (head restProgram) graph of
    [] -> False -- No matching edge found
    matchingEdges ->
      any (\(_, toState, _) ->
        validPath (tail restProgram) graph toState (toState:visitedStates)
      ) matchingEdges

-- Helper function to check if an iteration of a program matches a path
validIteration :: Program -> Graph -> State -> [State] -> Bool
validIteration restProgram graph currentState visitedStates =
  validPath restProgram graph currentState visitedStates ||
    any (\(_, toState, _) -> validSequence (p : '*' : restProgram) graph toState (toState:visitedStates)) matchingEdges
  where
    p = head restProgram
    matchingEdges = findMatchingEdges currentState p graph

-- Helper function to check if a non-deterministic choice between two programs matches a path
validChoice :: Program -> Graph -> State -> [State] -> Bool
validChoice restProgram graph currentState visitedStates =
  validPath restProgram graph currentState visitedStates ||
    validPath (dropWhile (/= 'U') restProgram) graph currentState visitedStates

-- Helper function to find edges that match the current state and atomic program
findMatchingEdges :: State -> Char -> Graph -> [LabeledEdge]
findMatchingEdges currentState atomicProgram graph =
  filter (\(fromState, _, program) -> fromState == currentState && program == [atomicProgram]) graph

main :: IO ()
main = do
  let program1 = "; a b"
      graph1 = [("s1", "s2", "a"), ("s2", "s1", "b")]
      result1 = validProgram program1 graph1
  putStrLn $ "Program: " ++ program1
  putStrLn $ "Graph: " ++ show graph1
  putStrLn $ "Result: " ++ show result1
  putStrLn ""

  let program2 = "; * a ; a b"
      graph2 = [("s1", "s2", "a"), ("s2", "s3", "a"), ("s3", "s4", "a"), ("s4", "s5", "b")]
      result2 = validProgram program2 graph2
  putStrLn $ "Program: " ++ program2
  putStrLn $ "Graph: " ++ show graph2
  putStrLn $ "Result: " ++ show result2
  putStrLn ""

