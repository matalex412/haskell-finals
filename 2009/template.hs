import Data.List
import Data.Maybe (fromJust)

type Index = Int

data BExp = Prim Bool | IdRef Index | Not BExp | And BExp BExp | Or BExp BExp
            deriving (Eq, Ord, Show)

type Env = [(Index, Bool)]

type NodeId = Int

type BDDNode =  (NodeId, (Index, NodeId, NodeId))

type BDD = (NodeId, [BDDNode])

------------------------------------------------------
-- PART I 40 mins

-- Pre: The item is in the given table
lookUp :: Eq a => a -> [(a, b)] -> b
lookUp x
  = fromJust . lookup x

checkSat :: BDD -> Env -> Bool
checkSat (r, ns) env
  = checkSat' r
  where
    checkSat' :: NodeId -> Bool
    checkSat' 0 
      = False
    checkSat' 1 
      = True
    checkSat' id
      = checkSat'
        $ if lookUp i env
            then r
            else l
      where
        (i, l, r) = lookUp id ns

sat :: BDD -> [[(Index, Bool)]]
sat (r, ns)
  = sat' r
  where
    sat' :: NodeId -> [[(Index, Bool)]]
    sat' 0 
      = []
    sat' 1 
      = [[]]
    sat' id
      = map ((i, True) :) (sat' r) ++
        map ((i, False) :) (sat' l)
      where
        (i, l, r) = lookUp id ns

  -- = filter (checkSat bdd) [ (i, b) | i <- is, b <- [True, False] ]
  -- where
  --   is = [1, 2] :: [Index]

------------------------------------------------------
-- PART II - 20 mins

simplify :: BExp -> BExp
simplify (Not (Prim b))
  = Prim (not b)
simplify (Or (Prim b) (Prim b'))
  = Prim (b || b')
simplify (And (Prim b) (Prim b'))
  = Prim (b && b')
simplify e
  = e

restrict :: BExp -> Index -> Bool -> BExp
restrict (IdRef i') i b | i' == i
  = Prim b
restrict (Not exp') i b
  = simplify (Not (restrict exp' i b))
restrict (And exp' exp'') i b
  = simplify (And (restrict exp' i b) (restrict exp'' i b))
restrict (Or exp' exp'') i b
  = simplify (Or (restrict exp' i b) (restrict exp'' i b))
restrict exp' _ _
  = exp'

------------------------------------------------------
-- PART III 50 mins


-- Pre: Each variable index in the BExp appears exactly once
--     in the Index list; there are no other elements
-- The question suggests the following definition (in terms of buildBDD')
-- but you are free to implement the function differently if you wish.
buildBDD :: BExp -> [Index] -> BDD
buildBDD e
  = buildBDD' e 2

-- Potential helper function for buildBDD which you are free
-- to define/modify/ignore/delete/embed as you see fit.
buildBDD' :: BExp -> NodeId -> [Index] -> BDD
buildBDD' (Prim True) id []
  = (1, [])
buildBDD' (Prim False) id []
  = (0, [])
buildBDD' e id (x : xs)
  = case (e', e'') of
      (Prim _, Prim _) 
        -> (id, [(id, (x, id', id''))])
      _
        -> (id, (id, (x, 2 * id, 2 * id + 1)) : ns ++ ns')
  where
    e'        = restrict e x False
    e''       = restrict e x True
    (id', ns)   = buildBDD' e' (2 * id) xs
    (id'', ns') = buildBDD' e'' (2 * id + 1) xs

------------------------------------------------------
-- PART IV

-- Pre: Each variable index in the BExp appears exactly once
--      in the Index list; there are no other elements
buildROBDD :: BExp -> [Index] -> BDD
buildROBDD e xs
  = tillConst (shareSubtrees . eliminate) (buildBDD e xs)

tillConst :: Eq a => (a -> a) -> a -> a
tillConst f xs
  | xs' == xs  = xs
  | otherwise  = tillConst f xs'
  where
    xs' = f xs

eliminate :: BDD -> BDD
eliminate (root, ns)
  = (root, map fixParent ns')
  where
    xys  = [ (x, l) | (x, (_, l, r)) <- ns, l == r ]
    ns'  = filter (\(_, (_, l, r)) -> l /= r) ns

    fixParent :: BDDNode -> BDDNode
    fixParent n@(x, (i, l, r))
      = (x, (i, l', r'))
      where
        l' = case (lookup l xys) of
              Just y -> y
              Nothing -> l
        r' = case (lookup l xys) of
              Just y -> y
              Nothing -> r


share :: [BDDNode] -> [BDDNode] -> [BDDNode]
share [] ns'
  = ns'
share (a@(id, n@(i, l, r)) : ns) ns'
  | null same = share ns ns'
  | otherwise = share ns (map fixParent (delete a ns'))

  where
    same = [ id' | (id', n') <- ns, n' == n, id' /= id ]
    
    fixParent :: BDDNode -> BDDNode
    fixParent n@(id', (i, l, r)) 
      | l == id   = (id', (i, head same, r))
      | r == id   = (id', (i, l, head same))
      | otherwise = n

shareSubtrees :: BDD -> BDD
shareSubtrees (root, ns)
  = (root, share ns ns)

------------------------------------------------------
-- Examples for testing...

b1, b2, b3, b4, b5, b6, b7, b8 :: BExp
b1 = Prim False
b2 = Not (And (IdRef 1) (Or (Prim False) (IdRef 2)))
b3 = And (IdRef 1) (Prim True)
b4 = And (IdRef 7) (Or (IdRef 2) (Not (IdRef 3)))
b5 = Not (And (IdRef 7) (Or (IdRef 2) (Not (IdRef 3))))
b6 = Or (And (IdRef 1) (IdRef 2)) (And (IdRef 3) (IdRef 4))
b7 = Or (Not (IdRef 3)) (Or (IdRef 2) (Not (IdRef 9)))
b8 = Or (IdRef 1) (Not (IdRef 1))

bdd1, bdd2, bdd3, bdd4, bdd5, bdd6, bdd7, bdd8 :: BDD
bdd1 = (0,[])
bdd2 = (2,[(4,(2,1,1)),(5,(2,1,0)),(2,(1,4,5))])
bdd3 = (5,[(5,(1,0,1))])
bdd4 = (2,[(2,(2,4,5)),(4,(3,8,9)),(8,(7,0,1)),(9,(7,0,0)),
           (5,(3,10,11)),(10,(7,0,1)),(11,(7,0,1))])
bdd5 = (3,[(4,(3,8,9)),(3,(2,4,5)),(8,(7,1,0)),(9,(7,1,1)),
           (5,(3,10,11)),(10,(7,1,0)),(11,(7,1,0))])
bdd6 = (2,[(2,(1,4,5)),(4,(2,8,9)),(8,(3,16,17)),(16,(4,0,0)),
           (17,(4,0,1)),(9,(3,18,19)),(18,(4,0,0)),(19,(4,0,1)),
           (5,(2,10,11)),(10,(3,20,21)),(20,(4,0,0)),(21,(4,0,1)),
           (11,(3,22,23)),(22,(4,1,1)),(23,(4,1,1))])
bdd7 = (6,[(6,(2,4,5)),(4,(3,8,9)),(8,(9,1,1)),(9,(9,1,0)),
           (5,(3,10,11)),(10,(9,1,1)),(11,(9,1,1))])
bdd8 = (2,[(2,(1,1,1))])

