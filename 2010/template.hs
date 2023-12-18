import Data.List (maximumBy)
import Data.Ord (comparing)

data SuffixTree = Leaf Int | Node [(String, SuffixTree)] 
                deriving (Eq, Show)

------------------------------------------------------

isPrefix :: String -> String -> Bool
isPrefix xs ys 
  = xs == (take (length xs) ys)

removePrefix :: String -> String -> String
removePrefix xs ys
--Pre: s is a prefix of s'
  = drop (length xs) ys

suffixes :: [a] -> [[a]]
suffixes xs
  = take (length xs) (iterate tail xs)
--   = [drop n xs | n <- [0 .. length xs - 1]]

isSubstring :: String -> String -> Bool
isSubstring xs ys
  = any (isPrefix xs) (suffixes ys)

findSubstrings :: String -> String -> [Int]
findSubstrings xs ys
  = [ length ys - length zs  | zs <- suffixes ys, isPrefix xs zs ]

------------------------------------------------------

-- part 2 1:36 left
getIndices :: SuffixTree -> [Int]
getIndices (Leaf n)
  = [n]
getIndices (Node ats)
  = concatMap (\(_, t) -> getIndices t) ats
-- getIndices . snd

partition :: String -> String -> (String, String, String)
partition xs ys
  = (cs, removePrefix cs xs, removePrefix cs ys)
  where cs = commonPrefix xs ys
        commonPrefix :: Eq a => [a] -> [a] -> [a]
        commonPrefix (x : xs) (y : ys)
         | x == y    = x : commonPrefix xs ys
         | otherwise = []
        commonPrefix _ _
         = []


findSubstrings' :: String -> SuffixTree -> [Int]
findSubstrings' _ (Leaf _)  = []
findSubstrings' xs (Node sts) 
  = concatMap checkSubtree sts
  where checkSubtree :: (String, SuffixTree) -> [Int]
        checkSubtree (ys, t)
         | null xs'  = getIndices t
         | null ys'  = findSubstrings' xs' t 
         | otherwise = []
         where
            (p, xs', ys') = partition xs ys

------------------------------------------------------

insert :: (String, Int) -> SuffixTree -> SuffixTree
insert (s, n) (Node [])
  = Node [(s, Leaf n)]
insert (s, n) (Node ((a, t) : ats))
  | null p    = Node ((a, t) : ats')
  | null a'   = Node ((a, insert (s', n) t) : ats)
  | otherwise = Node ((p, Node [(s', Leaf n), (a', t)]) : ats)
  where 
    (p, s', a') = partition s a
    Node ats'   = insert (s, n) (Node ats)

-- This function is given
buildTree :: String -> SuffixTree 
buildTree s
  = foldl (flip insert) (Node []) (zip (suffixes s) [0..])

------------------------------------------------------
-- Part IV

-- longestRepeatedSubstring :: SuffixTree -> String
-- longestRepeatedSubstring (Leaf _)
--  = "Not valid word"
-- longestRepeatedSubstring (Node ats) 
--  = case (filter hasRepeats ats) of
--     []  -> "No repeats"
--     rs  -> head $ sortBy lengthSort (map helper rs)
--     where   hasRepeats :: (String, SuffixTree) -> Bool
--             hasRepeats (a, (Node ats)) = length ats >= 2 
--             hasRepeats _               = False

--             helper (s, Node ats) 
--                 | not (any hasRepeats ats) = s
--                 | otherwise                = s ++ longestRepeatedSubstring (Node ats)

--             lengthSort :: String -> String -> Ordering
--             lengthSort xs ys = compare (- length xs) (- length ys)

-- can also use snd . maximum after zipping lengths
longestRepeatedSubstring :: SuffixTree -> String
longestRepeatedSubstring (Node ats) 
 =  maximumBy (comparing length) [ getSubstring at | at <- ats, hasRepeats at ]
    where   hasRepeats :: (String, SuffixTree) -> Bool
            hasRepeats (_, (Node ats)) = length ats >= 2 
            hasRepeats _               = False

            getSubstring (s, Node ats) 
                | not (any hasRepeats ats) = s
                | otherwise                = s ++ longestRepeatedSubstring (Node ats)

------------------------------------------------------
-- Example strings and suffix trees...

s1 :: String
s1 
  = "banana"

s2 :: String
s2 
  = "mississippi"

t1 :: SuffixTree
t1 
  = Node [("banana", Leaf 0), 
          ("a", Node [("na", Node [("na", Leaf 1), 
                                   ("", Leaf 3)]), 
                     ("", Leaf 5)]), 
          ("na", Node [("na", Leaf 2), 
                       ("", Leaf 4)])]

t2 :: SuffixTree
t2 
  = Node [("mississippi", Leaf 0), 
          ("i", Node [("ssi", Node [("ssippi", Leaf 1), 
                                    ("ppi", Leaf 4)]), 
                      ("ppi", Leaf 7), 
                      ("", Leaf 10)]), 
          ("s", Node [("si", Node [("ssippi", Leaf 2), 
                                   ("ppi", Leaf 5)]), 
                      ("i", Node [("ssippi", Leaf 3), 
                                  ("ppi", Leaf 6)])]), 
          ("p", Node [("pi", Leaf 8), 
                      ("i", Leaf 9)])]