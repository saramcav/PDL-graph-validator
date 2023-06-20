import Data.List (nub)

type State = String
type Edge = (State, State)

getPossibleTransitives :: [Edge] -> [Edge] -> [Edge]
getPossibleTransitives edges1 edges2 =
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
