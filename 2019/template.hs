module SOL where

import Data.Ord (comparing)
import Data.List
import Data.Maybe
import Data.Tuple (swap)

import Types
import TestData

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp k xys
  = head [ y | (x, y) <- xys, x == k]
-- fromJust (lookup x xys)

-- 3 marks
-- if all cases have function applied, it can be refactored e.g sort . nub
vars :: Formula -> [Id]
vars (Var x)
  = [x]
vars (Not f)
  = vars f
vars (And f f')
  = sort (nub (vars f ++ vars f'))
vars (Or f f')
  = sort (nub (vars f ++ vars f'))

-- 1 mark
idMap :: Formula -> IdMap
idMap f
  = zip (vars f) [1..]

--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF (Not (Not f))
  = toNNF f
toNNF (Not (Or f f'))
  = And (toNNF (Not f)) (toNNF (Not f'))
toNNF (Not (And f f'))
  = Or (toNNF (Not f)) (toNNF (Not f'))
toNNF (Or f f')
  = Or (toNNF f) (toNNF f')
toNNF (And f f')
  = And (toNNF f) (toNNF f')
toNNF x
  = x

-- 3 marks
-- look for point-free
toCNF :: Formula -> CNF
toCNF
  = toCNF' . toNNF
  where
    toCNF' :: NNF -> CNF
    toCNF' (Or f f')
      = distribute (toCNF f) (toCNF f')
    toCNF' (And f f')
      = And (toCNF f) (toCNF f')
    toCNF' x
      = x

-- 4 marks
flatten :: CNF -> CNFRep
-- don't over try for point free
flatten f = flatten' f
    where 
        ids = idMap f
        flatten' :: CNF -> CNFRep
        flatten' (Var x) 
          = [[lookUp x ids]]
        flatten' (Not (Var x))
          = [[negate (lookUp x ids)]]
        flatten' (Or l l')
          = [concat (flatten' l ++ flatten' l')]
        flatten' (And c c')
          = flatten' c ++ flatten' c'

-- 1hr 33 mins
--------------------------------------------------------------------------
-- Part III

-- 5 marks
-- propUnits :: CNFRep -> (CNFRep, [Int])
-- propUnits xss 
--   = case findUnit xss of
--         0 -> (xss, [])
--         x -> propUnits' xss x ([], [])
--   where
--     findUnit :: CNFRep -> Int
--     findUnit []
--       = 0
--     findUnit ([x] : xss)
--       = x
--     findUnit (_ : xss)
--       = findUnit xss

--     propUnits' :: CNFRep -> Int -> (CNFRep, [Int]) -> (CNFRep, [Int])
--     propUnits' [] x (xss, xs)
--       = case (findUnit xss) of
--             0 -> (xss, (x : xs))
--             n -> propUnits' xss n ([], x : xs)
--     propUnits' (ys : yss) x (xss, xs)
--       | x `elem` ys        = propUnits' yss x (xss, xs)
--       | negate x `elem` ys = propUnits' yss x (delete (negate x) ys : xss, xs)
--       | otherwise          = propUnits' yss x (ys : xss, xs)

-- avoid unnecessary helpers
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits xss 
  | u == 0    = (xss, [])
  | otherwise = (xss'', u : xs)
  where
    findUnit :: CNFRep -> Int
    findUnit ([x] : xss) 
      = x
    findUnit (_ : xss)
      = findUnit xss
    findUnit []
      = 0

    u           = findUnit xss
    xss'        = (map (delete (negate u)) . filter (u `notElem`)) xss
    (xss'', xs) = propUnits xss'

-- 4 marks
-- consider simplest case first

-- any null better than [] `elem`
-- dp :: CNFRep -> [[Int]]
-- dp xss
--   = map (us ++) (concatMap (dp' xss') ids)
--   where
--     (xss', us) = propUnits xss
--     id = head (concat xss')
--     ids = [id, negate id]

--     dp' :: [[Int]] -> Int -> [[Int]]
--     dp' xss x 
--         | null xss'      = [us']
--         | any null xss'  = []
--         | otherwise      = map (x :) (dp xss')
--         where
--         (xss', us') = propUnits ([x] : xss)

dp :: CNFRep -> [[Int]]
dp xss
  | null xss'     = [us]
  | any null xss' = []
  | otherwise     = map (us ++) (concatMap (\x -> dp ([x] : xss')) ids)
  where
    (xss', us) = propUnits xss
    id         = head (concat xss')
    ids        = [id, negate id]


--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat f
  = (sort . map (map assign) . concatMap addMissing . dp . flatten . toCNF) f
  where
    vs = vars f
    ids = (map swap . idMap) f

    assign :: Int -> (Id, Bool)
    assign x
      | x > 0     = (lookUp x ids, True)
      | otherwise = (lookUp (negate x) ids, False)

    is = (map fst ids)
    addMissing :: [Int] -> [[Int]]
    addMissing xs
      | null vs'   = [xs]
      | otherwise = concatMap addMissing [v : xs, negate v : xs]
      where
        vs' = is \\ map abs xs
        (v : _) = vs'
        