module Alloc where

import Data.Maybe
import Data.List
import Data.Tuple (swap)
import Data.Char (ord, chr)

import Types
import Examples

------------------------------------------------------
--
-- Part I
--
count :: Eq a => a -> [a] -> Int
count x
  = length . filter (== x)


-- unzip could be used

degrees :: Eq a => Graph a -> [(a, Int)]
degrees (ns, es)
  = map (\n -> (n, count n endpoints)) ns
  where
    endpoints = map fst es ++ map snd es

neighbours :: Eq a => a -> Graph a -> [a]
neighbours n (ns, es)
  = nub ([ start | (start, end) <- es, end == n] ++
         [ end | (start, end) <- es, start == n])

removeNode :: Eq a => a -> Graph a -> Graph a
removeNode n (ns, es)
  = (delete n ns, [ e | e@(start, end) <- es, start /= n, end /= n])

------------------------------------------------------
--
-- Part II
--

-- could have done ++ [0] to csLeft to ensure not empty then use head
-- instead of guards

colourGraph :: (Ord a, Show a) => Int -> Graph a -> Colouring a
colourGraph _ ([], _)
  = []
colourGraph maxC g@(ns, es)
  | null csLeft = (n, 0) : cMap
  | otherwise   = (n, head csLeft) : cMap
  where
    (_, n) = minimum (map swap (degrees g))
    g'     = removeNode n g
    cMap   = colourGraph maxC g'
    csLeft = [1..maxC] \\ (map (`lookUp` cMap) (neighbours n g))


------------------------------------------------------
--
-- Part III
--
buildIdMap :: Colouring Id -> IdMap
buildIdMap idcs
  = ("return", "return") : map mapVar idcs
  where
    mapVar :: (Id, Int) -> (Id, Id)
    mapVar (id, 0)
      = (id, id)
    mapVar (id, n)
      = (id, 'R' : show n)

buildArgAssignments :: [Id] -> IdMap -> [Statement]
buildArgAssignments ids idMap
  = [ Assign id' (Var id) | id <- ids
                          , id' <- [lookUp id idMap]
                          , id' /= id ]


renameExp :: Exp -> IdMap -> Exp
-- Pre: A precondition is that every variable referenced in 
-- the expression is in the idMap. 
renameExp (Var id) idMap
  = Var (lookUp id idMap)
renameExp (Apply op e e') idMap
  = Apply op (renameExp e idMap) (renameExp e' idMap)
renameExp e _
  = e


-- could have performed a map and then filtered out self-assignments
-- instead of recursion

renameBlock :: Block -> IdMap -> Block
-- Pre: A precondition is that every variable referenced in 
-- the block is in the idMap. 
renameBlock b idMap 
  = renameBlock' b 
  where
    renameBlock' :: Block -> Block
    renameBlock' []
      = []
    renameBlock' (Assign id e : sments)
      = case renameExp e idMap of
          Var id'' | id' == id''
            -> renameBlock' sments
          e'
            -> Assign id' e' : renameBlock' sments
      where
        id' = lookUp id idMap
    renameBlock' (If e b b' : sments)
      = If (renameExp e idMap) (renameBlock' b) (renameBlock' b') 
      : renameBlock' sments
    renameBlock' (While e b : sments)
      = While (renameExp e idMap) (renameBlock' b)
      : renameBlock' sments

renameFun :: Function -> IdMap -> Function
renameFun (f, as, b) idMap
  = (f, as, buildArgAssignments as idMap ++ renameBlock b idMap)

-----------------------------------------------------
--
-- Part IV
--

buildIG :: [[Id]] -> IG
buildIG idss
  = (ids, nub [(start, end) | liveVars <- idss
                            , start <- liveVars
                            , end <- liveVars
                            , start < end])
  where
    ids = nub (concat idss)

-----------------------------------------------------
--
-- Part V
--



liveVars :: CFG -> [[Id]]
liveVars cfg
  = tillConst (getLiveVars 0) (replicate l [])
  where
    l = length cfg
    getLiveVars :: Int -> [[Id]] -> [[Id]]
    getLiveVars n idss 
      | n >= l    = []
      | otherwise = (nub ((use ++ concatMap (idss !!) succs) \\ [def])) 
                  : getLiveVars (n + 1) idss
      where
        ((def, use), succs) = cfg !! n

tillConst f y
  | f y == y  = y
  | otherwise = tillConst f (f y)


buildCFG :: Function -> CFG
buildCFG (_, _, b)
  = buildCFG' 0 b
  where
    buildCFG' :: Int -> Block -> CFG
    buildCFG' _ []
      = []
    buildCFG' n (Assign id e : sments)
      | id == "return" = ((id, vars e), []) : buildCFG' (n + 1) sments
      | otherwise      = ((id, vars e), [n + 1]) : buildCFG' (n + 1) sments
    buildCFG' n (If e b b' : sments)
      = (("_", vars e), [n + 1, n + length cfg' + 1]) 
      : cfg' ++ cfg'' ++ buildCFG' (n + length cfg' + length cfg'' + 1) sments
      where
        cfg'  = buildCFG' (n + 1) b
        cfg'' = buildCFG' (n + length cfg' + 1) b'
    buildCFG' n (While e b : sments)
      = (("_", vars e), [n + 1, n + 1 + length cfg']) 
      : cfg' ++ buildCFG' (n + length cfg' + 1) sments
      where
        cfg'' = buildCFG' (n + 1) b
        ((def, use), succs) = last cfg''
        cfg' = init cfg'' ++ [((def, use), [n])]


    vars :: Exp -> [Id]
    vars (Var id)
      = [id]
    vars (Apply _ e e')
      = nub (vars e ++ vars e')
    vars _
      = []

-- fun f(a, n) {
-- 0: b = 0;
-- 1: while (n >= 1) {
-- 2:   c = a + b;
-- 3:   d = c + b;
-- 4:   if (d >= 20) {
-- 5:     b = c + d;
-- 6:     d = d + 1;
--      }
-- 7:   a = c * d;
-- 8:   n = n + -1;
--    }
-- 9: return = d;
-- }