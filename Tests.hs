type State = String
type Edge = (State, State)

getReflexivePossibilities::[Edge] -> [Edge]
getReflexivePossibilities edges = let reflexives1 = [(fromState, fromState) | (fromState, toState) <- edges] 
                                      reflexives2 = [(toState, toState) | (fromState, toState) <- edges]
                                      in unionEdges reflexives1 reflexives2

unionEdges :: [Edge] -> [Edge] -> [Edge]
unionEdges edges1 edges2 = edges1 ++ filter (`notElem` edges1) edges2

main = do

    let graph1_prog1 = [("s1", "s2"), ("s1", "s3")]

    putStrLn "Resultado do Programa 1:"
    putStrLn ("O resultado do caso 1 é: " ++ show (getReflexivePossibilities graph1_prog1))
