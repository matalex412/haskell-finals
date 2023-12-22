module Tries where

import Data.Char (digitToInt)
import Data.List hiding (insert)
import Data.Bits

import Types
import HashFunctions
import Examples

--------------------------------------------------------------------
-- Part I

-- Use this if you're counting the number of 1s in every
-- four-bit block...
bitTable :: [Int]
bitTable
  = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

countOnes :: Int -> Int
countOnes 0
  = 0
countOnes x 
  = bitTable !! r + countOnes q
  where
    (q, r) = quotRem x 16

-- use built in functions where option given for safety
countOnesFrom :: Int -> Int -> Int
countOnesFrom i n
  = countOnes (n .&. (bit i - 1))

getIndex :: Int -> Int -> Int -> Int
getIndex n i b
  = shiftR n (i * b) .&. (bit b - 1)


-- Pre: the index is less than the length of the list
replace :: Int -> [a] -> a -> [a]
replace 0 (x : xs) y
  = y : xs
replace n (x : xs) y
  = x : replace (n - 1) xs y

-- Pre: the index is less than or equal to the length of the list
insertAt :: Int -> a -> [a] -> [a]
insertAt 0 y xs
  = y : xs
insertAt n y (x : xs)
  = x : insertAt (n - 1) y xs

--------------------------------------------------------------------
-- Part II

sumTrie :: (Int -> Int) -> ([Int] -> Int) -> Trie -> Int
sumTrie _ g (Leaf xs)
  = g xs
sumTrie f g (Node _ ns)
  = sum (map sumSubNode ns)
  where
    sumSubNode :: SubNode -> Int
    sumSubNode (Term x) 
      = f x
    sumSubNode (SubTrie t)
      = sumTrie f g t

--
-- If you get the sumTrie function above working you can uncomment
-- these three functions; they may be useful in testing.
--
trieSize :: Trie -> Int
trieSize t
  = sumTrie (const 1) length t

binCount :: Trie -> Int
binCount t
  = sumTrie (const 1) (const 1) t

meanBinSize :: Trie -> Double
meanBinSize t
  = fromIntegral (trieSize t) / fromIntegral (binCount t)

member :: Int -> Hash -> Trie -> Int -> Bool
member x h t b
  = member' t 0
  where
    member' :: Trie -> Int -> Bool
    member' (Leaf xs) _
      = x `elem` xs
    member' (Node bv ns) l
      = let i = getIndex h l b in
            testBit bv i && 
            case (ns !! (countOnesFrom i bv)) of
                Term y     -> x == y
                SubTrie t' -> member' t' (l + 1)



--------------------------------------------------------------------
-- Part III

-- don't under do how many arguments in helper
-- label variables same as spec e.g. v not x
-- use different letter variable names for helper
-- when writing variable names check carefully not used already
-- label indices as i, i' etc. not different letters
-- consider what 'state' needs to be maintained in recursion
-- item being changed should be last argument
insert :: HashFun -> Int -> Int -> Int -> Trie -> Trie
insert f d b x t
  = insert' x t 0
  where
    insert' :: Int -> Trie -> Int -> Trie
    insert' x (Leaf xs) l
      = Leaf (nub (x : xs))
    insert' x _ l | l == (d - 1)
      = Leaf [x]
    insert' x (Node bv ns) l
      | testBit bv i 
        = Node bv (replace i' ns node)
      | otherwise    
        = Node (setBit bv i) (insertAt i' (Term x) ns)
      where 
        i  = getIndex (f x) l b 
        i' = countOnesFrom i bv

        node 
          = case (ns !! i') of
              SubTrie t' 
                -> SubTrie (insert' x t' (l + 1))
              Term x'   
                -> if (x' == x)
                    then Term x'
                    else SubTrie (insert' x (insert' x' empty (l + 1)) (l + 1))
                    -- else SubTrie (insert' x (insert f (d - (l + 1)) b x' empty) (l + 1))

-- check if variables can be removed in fold function
buildTrie :: HashFun -> Int -> Int -> [Int] -> Trie
buildTrie f d b
  = foldr (insert f d b) empty