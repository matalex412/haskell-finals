import Data.List (minimumBy)
import Data.Ord (comparing)

type BinHeap a = [BinTree a]

data BinTree a = Node a Int (BinHeap a)
               deriving (Eq, Ord, Show)

--------------------------------------------------------------
-- PART I

value :: BinTree a -> a
value (Node x _ _)
  = x

rank :: BinTree a -> Int
rank (Node _ r _)
  = r

children :: BinTree a -> [BinTree a]
children (Node _ _ ts)
  = ts

-- combineTrees :: Ord a => BinTree a -> BinTree a -> BinTree a
-- combineTrees t1 t2
--   = Node (value rt) (rank rt + 1) (ct : children rt)
--   where (rt, ct) = if (value t1 < value t2) then (t1, t2) else (t2, t1)

-- pattern matching cleaner than extractor functions
combineTrees :: Ord a => BinTree a -> BinTree a -> BinTree a
combineTrees t@(Node v r h) t'@(Node v' _ h')
  | v < v'    = Node v (r + 1) (t' : h)
  | otherwise = Node v' (r + 1) (t : h')


--------------------------------------------------------------
-- PART II

extractMin :: Ord a => BinHeap a -> a
extractMin
  = minimum . map value

-- pattern matching better than head and tail
-- t, t' preferred to t1, t2
mergeHeaps :: Ord a => BinHeap a -> BinHeap a -> BinHeap a
mergeHeaps lh []
  = lh
mergeHeaps [] rh
  = rh
mergeHeaps h@(t : ts) h'@(t' : ts')
  | rank t < rank t'   
    = t : mergeHeaps ts h'
  | rank t' < rank t    
    = t' : mergeHeaps ts' h
  | otherwise            
    = mergeHeaps [combineTrees t t'] (mergeHeaps ts ts')


-- check for point free
insert :: Ord a => a -> BinHeap a -> BinHeap a
insert x
  = mergeHeaps [Node x 0 []]

-- comments for helper functions
-- deleteMin :: Ord a => BinHeap a -> BinHeap a
-- deleteMin []
--   = []
-- deleteMin h
--   = mergeHeaps (reverse (children rt)) remH
--   where (rt, remH) = removeMin h

-- remove :: Eq a => a -> BinHeap a -> BinHeap a
-- remove _ [] = [] 
-- remove v (t:ts)
--  | value t == v  = ts
--  | otherwise     = t : remove v ts

-- removeMin :: Ord a => BinHeap a -> (BinTree a, BinHeap a)
-- removeMin h
--   = (rt, remove (value rt) h)
--   where rt = minimumBy (comparing value) h

-- remember edge case [] when using minimum
deleteMin :: Ord a => BinHeap a -> BinHeap a
deleteMin []
  = []
deleteMin h
  = mergeHeaps (reverse (children rt)) [t | t <- h, t /= rt]
  where rt = minimumBy (comparing value) h

-- if reverse needed try switch from tail recursion
binSort :: Ord a => [a] -> [a]
binSort xs
  = sort (foldr insert [] xs)
  where sort :: Ord a => BinHeap a -> [a]
        sort []
          = []
        sort h 
          = extractMin h : sort (deleteMin h)

--------------------------------------------------------------
-- PART III

-- toBinary :: BinHeap a -> [Int]
-- toBinary ts
--   = numNodes [0..maxR] []
--   where rs = map rank ts
--         maxR  = maximum rs

--         numNodes :: [Int] -> [Int] -> [Int]
--         numNodes [] xs 
--           = xs
--         numNodes (i : is) xs
--          | i `elem` rs = numNodes is (1 : xs)
--          | otherwise   = numNodes is (0 : xs)

-- making use of ordering of binheap
toBinary :: BinHeap a -> [Int]
toBinary ts
  = numNodes ts []
  where numNodes :: BinHeap a -> [Int] -> [Int]
        numNodes [] xs
          = xs
        numNodes h@(t : ts) xs
          | rank t == length xs  = numNodes ts (1 : xs)
          | otherwise            = numNodes h (0 : xs)

binarySum :: [Int] -> [Int] -> [Int]
binarySum xs ys
  = adder (reverse xs') (reverse ys') 0 []
  where l = max (length xs) (length ys)
        xs' = until (\zs -> length zs == l) (0 : ) xs
        ys' = until (\zs -> length zs == l) (0 : ) ys

        adder :: [Int] -> [Int] -> Int -> [Int] -> [Int]
        adder (x : xs) (y : ys) c res
          | sum <= 1  = adder xs ys 0 (sum : res)
          | otherwise = adder xs ys 1 (sum `mod` 2 : res)
          where sum = x + y + c
        adder _ _ 0 res = res
        adder _ _ 1 res = 1 : res

------------------------------------------------------
-- Some sample trees...

t1, t2, t3, t4, t5, t6, t7, t8 :: BinTree Int
-- Note: t7 is the result of merging t5 and t6

-- t1 to t4 appear in Figure 1...
t1 = Node 4 0 []
t2 = Node 1 1 [Node 5 0 []]
t3 = Node 2 2 [Node 8 1 [Node 9 0 []], 
               Node 7 0 []]
t4 = Node 2 3 [Node 3 2 [Node 6 1 [Node 8 0 []], 
                         Node 10 0 []],
               Node 8 1 [Node 9 0 []],
               Node 7 0 []]

-- t5 and t6 are on the left of Figure 2; t7 is on the
-- right
t5 = Node 4 2 [Node 6 1 [Node 8 0 []], 
                         Node 10 0 []]
t6 = Node 2 2 [Node 8 1 [Node 9 0 []], Node 7 0 []]
t7 = Node 2 3 [Node 4 2 [Node 6 1 [Node 8 0 []], Node 10 0 []],
               Node 8 1 [Node 9 0 []], 
               Node 7 0 []]

-- An additional tree...
t8 = Node 12 1 [Node 16 0 []]

------------------------------------------------------
-- Some sample heaps...

h1, h2, h3, h4, h5, h6, h7 :: BinHeap Int
-- Two arbitrary heaps for testing...
h1 = [t2, t7]
h2 = [Node 1 2 [Node 12 1 [Node 16 0 []],
                Node 5 0 []],
      Node 2 3 [Node 4 2 [Node 6 1 [Node 8 0 []],
                          Node 10 0 []],
                Node 8 1 [Node 9 0 []],
                Node 7 0 []]]

-- h3 is shown in Figure 3...
h3 = [t1, t2, t4]

-- Two additional heaps, used below. They are shown
-- in Figure 4(a)...

h4 = [t2, t5]
h5 = [t1, t8]

-- h6 is the result of merging h4 and h5, shown in Figure 4(b)...
h6 = [Node 4 0 [],
      Node 1 3 [Node 4 2 [Node 6 1 [Node 8 0 []],
                          Node 10 0 []],
                Node 12 1 [Node 16 0 []],
                Node 5 0 []]]

-- h7 is shown in Figure 5...
h7 = [Node 4 3 [Node 4 2 [Node 12 1 [Node 16 0 []],
                          Node 5 0 []],
                Node 6 1 [Node 8 0 []],
                Node 10 0 []]]


