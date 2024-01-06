import Data.List
import Data.Maybe (fromJust)
import Data.Ord (comparing)

type Index = Int

data BExp = Prim Bool | IdRef Index | Not BExp | And BExp BExp | Or BExp BExp
            deriving (Eq, Ord, Show)

type Env = [(Index, Bool)]

type NodeId = Int

type BDDNode =  (NodeId, (Index, NodeId, NodeId))

type BDD = (NodeId, [BDDNode])

------------------------------------------------------
-- PART I

-- Pre: The item is in the given table
lookUp :: Eq a => a -> [(a, b)] -> b
lookUp x
  = fromJust . lookup x

-- walk from top to bottom of bdd
-- lookUp current nodeId in BDD
-- lookUp vId (while in a node) in env
checkSat :: BDD -> Env -> Bool
checkSat (root, ns) env 
  = travel root
  where
    travel :: NodeId -> Bool
    travel 0
      = False
    travel 1
      = True
    travel nId
      | lookUp vId env = travel right
      | otherwise      = travel left
      where
        (vId, left, right) = lookUp nId ns

sat :: BDD -> [[(Index, Bool)]]
sat (root, ns)
  = travel root
  where
    travel :: NodeId -> [[(Index, Bool)]]
    travel 0
      = []
    travel 1
      = [[]]
    travel nId
      = map ((vId, False) :) (travel left) ++ map ((vId, True) :) (travel right)
      where
        (vId, left, right) = lookUp nId ns

------------------------------------------------------
-- PART II


simplify :: BExp -> BExp
simplify (Not (Prim b))
  = Prim (not b)
simplify (And (Prim b) (Prim b'))
  = Prim (b && b')
simplify (Or (Prim b) (Prim b'))
  = Prim (b || b')
simplify (And e e')
  = And (simplify e) (simplify e')
simplify (Or e e')
  = Or (simplify e) (simplify e')
simplify e
  = e

restrict :: BExp -> Index -> Bool -> BExp
restrict (IdRef vId') vId b | vId' == vId
  = Prim b
restrict (Not e) vId b
  = simplify (Not (restrict e vId b))
restrict (And e e') vId b
  = simplify (And (restrict e vId b) (restrict e' vId b))
restrict (Or e e') vId b
  = simplify (Or (restrict e vId b) (restrict e' vId b))
restrict e _ _
  = e

------------------------------------------------------
-- PART III

-- Pre: Each variable index in the BExp appears exactly once
--     in the Index list; there are no other elements
-- The question suggests the following definition (in terms of buildBDD')
-- but you are free to implement the function differently if you wish.
buildBDD :: BExp -> [Index] -> BDD
buildBDD e xs
  = buildBDD' e 2 xs

-- Potential helper function for buildBDD which you are free
-- to define/modify/ignore/delete/embed as you see fit.
buildBDD' :: BExp -> NodeId -> [Index] -> BDD
buildBDD' (Prim False) _ []
  = (0, [])
buildBDD' (Prim True) _ []
  = (1, [])
buildBDD' e nId (vId : vIds)
  = (nId, (nId, (vId, l, r)) : lNodes ++ rNodes)
  where
    (l, lNodes) = buildBDD' (restrict e vId False) (2 * nId) vIds
    (r, rNodes) = buildBDD' (restrict e vId True) (2 * nId + 1) vIds

------------------------------------------------------
-- PART IV

-- Pre: Each variable index in the BExp appears exactly once
--      in the Index list; there are no other elements
buildROBDD :: BExp -> [Index] -> BDD
buildROBDD e
  = tillConst (shareSubtree . eliminateNode) . buildBDD e

tillConst :: Eq a => (a -> a) -> a -> a
tillConst f x
  | f x == x  = x
  | otherwise = tillConst f (f x)

eliminateNode :: BDD -> BDD
eliminateNode bdd@(root, nodes)
  = case find (\(_, (_, l, r)) -> l == r) nodes of
      Just n@(nId, (vId, c, _))
        -> case delete n nodes of
            []
              -> (c, [])
            ns
              -> (root, map (amendParent nId c) ns)
      Nothing
        -> bdd

amendParent nId c n@(nId', (vId, l, r))
  | l == nId, r == nId  = (nId', (vId, c, c))
  | l == nId  = (nId', (vId, c, r))
  | r == nId  = (nId', (vId, l, c))
  | otherwise = n

shareSubtree :: BDD -> BDD
shareSubtree bdd@(root, ns)
  = case find ((> 1) . length) nss of
      Just (n@(nId, _) : n'@(nId', _) : ns')
        -> (root, map (amendParent nId nId') (delete n ns))
      Nothing -> bdd
  where
    nss = groupBy identical (sortBy (comparing snd) ns)

identical :: BDDNode -> BDDNode -> Bool
identical (_, (vId, l, r)) (_, (vId', l', r'))
  = (l == l') && (r == r') && (vId == vId')


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

