type State = String
type AtomicProgram = String
type NamedEdge = (State, State, AtomicProgram)
type Graph = [NamedEdge]

data PDLProgram = AtomicProgram String | OperatorProgram String [PDLProgram] deriving Show

"U a ; b c"
["U", "a", ...]
(1, 2, a)

(1, 3, b)
(3, 4, c)

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

evaluateProgram :: PDLProgram -> Graph -> Bool
evaluateProgram (AtomicProgram program) graph =
  any (\(_, _, atomicProgram) -> atomicProgram == program) graph
evaluateProgram (OperatorProgram op children) graph =
  case op of
    "U" -> any (\child -> evaluateProgram child graph) children
    ";" -> evaluateSequence children graph
    "*" -> evaluateIteration (head children) graph
    _ -> error "Invalid operator"

evaluateSequence :: [PDLProgram] -> Graph -> Bool
evaluateSequence [] _ = True
evaluateSequence [prog] graph = evaluateProgram prog graph
evaluateSequence (prog1 : prog2 : rest) graph =
  evaluateProgram prog1 graph && evaluateSequence (prog2 : rest) graph

evaluateIteration :: PDLProgram -> Graph -> Bool
evaluateIteration prog graph = evaluateIteration' prog graph []

evaluateIteration' :: PDLProgram -> Graph -> [State] -> Bool
evaluateIteration' prog graph visited =
  any (\(_, nextState, _) -> evaluateIteration' prog graph (nextState : visited)) validEdges
  where
    validEdges = filter (\(currentState, nextState, atomicProgram) ->
                           evaluateProgram prog [(currentState, nextState, atomicProgram)]) graph

main :: IO ()
main = do
  let pdlProgram = words "; a b"
  let programAST = parsePDL pdlProgram
  let graph = [("s1", "s2", "a"), ("s1", "s2", "b")]
  let isValid = evaluateProgram programAST graph
  print programAST
  putStrLn $ "Is graph valid for the program? " ++ show isValid
