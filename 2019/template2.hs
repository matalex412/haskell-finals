module SOL where

import Data.List
import Data.Maybe

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
lookUp x
  = fromJust . lookup x

-- 3 marks
vars :: Formula -> [Id]
vars
  = sort . nub . vars'

vars' (Var id)
  = [id]
vars' (Not f)
  = vars' f
vars' (And f f')
  = vars' f ++ vars' f'
vars' (Or f f')
  = vars' f ++ vars' f'


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
  = f
toNNF (Not (Or f f'))
  = And (toNNF (Not f)) (toNNF (Not f'))
toNNF (Not (And f f'))
  = Or (toNNF (Not f)) (toNNF (Not f'))
toNNF (Not f)
  = Not (toNNF f)
toNNF (And f f')
  = And (toNNF f) (toNNF f')
toNNF (Or f f')
  = Or (toNNF f) (toNNF f')
toNNF f
  = f

-- A ∨ (B ∧ C) ≡ (A ∨ B) ∧ (A ∨ C)
-- (A ∧ B) ∨ C ≡ (A ∨ C) ∧ (B ∨ C)


-- 3 marks
toCNF :: Formula -> CNF
toCNF
  = toCNF' . toNNF

toCNF' :: Formula -> CNF
toCNF' (Or f f')
  = distribute f f'
toCNF' (And f f')
  = And (toCNF' f) (toCNF' f')
toCNF' f
  = f


-- 4 marks
flatten :: CNF -> CNFRep
flatten f
  = flatten' f
  where
    t = idMap f

    flatten' (And f f')
      = flatten' f ++ flatten' f'
    flatten' (Or f f')
      = [concat (flatten' f ++ flatten' f')]
    flatten' (Not (Var id))
      = [[negate (lookUp id t)]]
    flatten' (Var id)
      = [[lookUp id t]]



--------------------------------------------------------------------------
-- Part III

-- 5 marks
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits cnfRep
  | null lits = (cnfRep, [])
  | otherwise = (cnfRep', lit : xs)
  where
    lits          = filter isLiteral cnfRep
    ([lit] : _)   = lits
    (cnfRep', xs) = propUnits (propUnit cnfRep)

    propUnit []
      = []
    propUnit (clause : cnfRep)
      | lit `elem` clause  = propUnit cnfRep
      | nLit `elem` clause = delete nLit clause : propUnit cnfRep
      | otherwise          = clause : propUnit cnfRep
      where
        nLit = negate lit

isLiteral :: [Int] -> Bool
isLiteral [_]
  = True
isLiteral _
  = False

-- 4 marks
dp :: CNFRep -> [[Int]]
dp cnfRep
  | null cnfRep'      = [xs]
  | [] `elem` cnfRep' = []
  | otherwise         = map (xs ++) (dp ([v] : cnfRep') ++ 
                                     dp ([negate v] : cnfRep'))
  where
    (cnfRep', xs) = propUnits cnfRep
    (v : _) = nub (concat cnfRep')

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat
  = undefined