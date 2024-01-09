module SC where

import Data.List
import Data.Maybe

import Types
import Examples

---------------------------------------------------------

prims :: [Id]
prims
  = ["+", "-", "*", "<=", "ite"]

lookUp :: Id -> [(Id, a)] -> a
lookUp v env
  = fromMaybe (error ("lookUp failed with search key " ++ v))
              (lookup v env)

---------------------------------------------------------
-- Part I


isFun :: Exp -> Bool
isFun (Fun _ _)
  = True
isFun _
  = False

splitDefs :: [Binding] -> ([Binding], [Binding])
splitDefs
  = partition (isFun . snd)


topLevelFunctions :: Exp -> Int
topLevelFunctions (Let bs _)
  = length (filter (isFun . snd) bs)
topLevelFunctions _
  = 0

---------------------------------------------------------
-- Part II

unionAll :: Eq a => [[a]] -> [a]
unionAll
  = foldr union []


freeVars :: Exp -> [Id]
freeVars (Var v) | v `notElem` prims
  = [v]
freeVars (App e as)
  = unionAll (map freeVars (e : as))
freeVars (Fun ps e)
  = freeVars e \\ ps
freeVars (Let bs e)
  = unionAll (map freeVars (e : es)) \\ ids
  where
    (ids, es) = unzip bs
freeVars _
  = []

---------------------------------------------------------
-- Part III

-- Given...
lambdaLift :: Exp -> Exp
lambdaLift e
  = lift (modifyFunctions (buildFVMap e) e)


buildFVMap :: Exp -> [(Id, [Id])]
buildFVMap (Let bs e)
  = zip fNames (repeat fvs) ++ concatMap buildFVMap (e : fes ++ nfes)
  where
    (fDefs, nfDefs) = splitDefs bs
    (fNames, fes)   = unzip fDefs
    (_, nfes)       = unzip nfDefs
    fvs             = sort (foldr (union . freeVars) [] fes \\ fNames)
buildFVMap (Fun _ e)
  = buildFVMap e
buildFVMap (App e as)
  = concatMap buildFVMap (e : as)
buildFVMap _
  = []

modifyFunctions :: [(Id, [Id])] -> Exp -> Exp
-- Pre: The mapping table contains a binding for every function
-- named in the expression.
modifyFunctions fvMap (Let bs e)
  = Let bs' (modifyFunctions fvMap e)
  where
    bs' = map modify bs

    modify :: Binding -> Binding
    modify (f, Fun as e)
      = ('$' : f, Fun (lookUp f fvMap ++ as) (modifyFunctions fvMap e))
    modify (id, v)
      = (id, modifyFunctions fvMap v)
modifyFunctions fvMap (Var f)
  = maybe (Var f) modify (lookup f fvMap)
  where
    modify fvs
      | null fvs  = Var ('$' : f)
      | otherwise = App (Var ('$' : f)) (map (\id -> Var id) fvs)
modifyFunctions _ c@(Const _)
  = c
modifyFunctions fvMap (App e as)
  = App (modifyFunctions fvMap e) (map (modifyFunctions fvMap) as)


-- The default definition here is id.
-- If you implement the above two functions but not this one
-- then lambdaLift above will remove all the free variables
-- in functions; it just won't do any lifting.
lift :: Exp -> Exp
lift e
  | null scs  = e'
  | otherwise = Let scs e'
  where
    (e', scs) = lift' e

-- You may wish to use this...
lift' :: Exp -> (Exp, [Supercombinator])
lift' (Let bs e)
  | null bs'' = (e', scs)
  | otherwise = (Let bs'' e', scs) 
  where
    (e', escs)   = lift' e
    (lscs, bs'') = partition (\(x : _, _) -> x == '$') bs'

    (ns, ds)     = unzip bs
    (ds', dscss) = unzip (map lift' ds)
    bs'          = zip ns ds'

    scs = lscs ++ escs ++ concat dscss
lift' (Fun ps e)
  = (Fun ps e', scs)
  where
    (e', scs) = lift' e
lift' (App f as)
  = (App f' as', fscs ++ concat ascss)
  where
    (f', fscs)   = lift' f
    (as', ascss) = unzip (map lift' as)
lift' e
  = (e, [])