module Solver where

import Data.List
import Data.Char

import Types
import WordData
import Clues
import Examples

------------------------------------------------------
-- Part I

punctuation :: String
punctuation 
  = "';.,-!?"

cleanUp :: String -> String
cleanUp
  = map toLower . filter (`notElem` punctuation)

split2 :: [a] -> [([a], [a])]
split2 xs
  = [ splitAt n xs | n <- [1..length xs - 1]]

split3 :: [a] -> [([a], [a], [a])]
split3 xs
  = [(x, y, z) | (x, w) <- split2 xs, (y, z) <- split2 w] ++
    [(x, [], z) | (x, z) <- split2 xs]

uninsert :: [a] -> [([a], [a])]
uninsert xs
  = [ (y, x ++ z) | (x, y, z) <- split3 xs, not (null y) ]

split2M :: [a] -> [([a], [a])]
split2M xs
  = sxs ++ [(y, x) | (x, y) <- sxs] 
  where
    sxs = split2 xs

split3M :: [a] -> [([a], [a], [a])]
split3M xs
  = sxs ++ [(z, y, x) | (x, y, z) <- sxs]
  where
    sxs = split3 xs


------------------------------------------------------
-- Part II


matches :: String -> ParseTree -> Bool
matches s (Synonym s')
  = s `elem` synonyms s'
matches s (Anagram _ s')
  = sort s == sort s'
matches s (Reversal _ t)
  = matches (reverse s) t
matches s (Insertion _ t1 t2)
  = or [ matches s1 t1 && matches s2 t2 | (s1, s2) <- uninsert s]
matches s (Charade _ t1 t2)
  = or [ matches s1 t1 && matches s2 t2 | (s1, s2) <- split2 s]
matches s (HiddenWord _ s')
  = or [ s == (concat . words) y | (_, y, _) <- split3 s'
                                 , length (filter (not . null) (words y)) == l]
  where
    l = length (words s')

evaluate :: Parse -> Int -> [String]
evaluate (d, _, t) n  
  = filter (\s -> (length s == n) && matches s t) (synonyms (unwords d))

------------------------------------------------------
-- Part III

-- Given...
parseWordplay :: [String] -> [ParseTree]
parseWordplay ws
  = concat [parseSynonym ws,
            parseAnagram ws,
            parseReversal ws,
            parseInsertion ws,
            parseHiddenWord ws,
            parseCharade ws]

parseSynonym :: [String] -> [ParseTree]
parseSynonym ws
  | (null . synonyms) s = []
  | otherwise           = [Synonym  s]
  where
    s = unwords ws

parseAnagram :: [String] -> [ParseTree]
parseAnagram ws
  = [Anagram ind (concat rest) | (ind, rest) <- split2M ws
                               , (unwords ind) `elem` anagramIndicators]

parseReversal :: [String] -> [ParseTree]
parseReversal ws
  = [Reversal ind t | (ind, rest) <- split2M ws
                    , (unwords ind) `elem` reversalIndicators
                    , t <- parseWordplay rest ]


parseInsertion :: [String] -> [ParseTree]
parseInsertion
  = parse2Arg insertionIndicators envelopeIndicators Insertion


parseCharade :: [String] -> [ParseTree]
parseCharade
  = parse2Arg beforeIndicators afterIndicators Charade


parse2Arg :: [String] 
          -> [String]
          -> (Indicator -> ParseTree -> ParseTree -> ParseTree) 
          -> [String] 
          -> [ParseTree]
parse2Arg inds inds' f ws
  = [f ind t1 t2 | (arg, ind, arg') <- split3 ws
                 , (unwords ind) `elem` inds
                 , t1 <- parseWordplay arg
                 , t2 <- parseWordplay arg'] ++
    [f ind t2 t1 | (arg, ind, arg') <- split3 ws
                 , (unwords ind) `elem` inds'
                 , t1 <- parseWordplay arg
                 , t2 <- parseWordplay arg']

parseHiddenWord :: [String] -> [ParseTree]
parseHiddenWord ws
  = [HiddenWord ind (unwords rest) | (ind, rest) <- split2M ws
                                   , (unwords ind) `elem` hiddenWordIndicators]

-- Given...
parseClue :: Clue -> [Parse]
parseClue clue@(s, n)
  = parseClueText (words (cleanUp s))

parseClueText :: [String] -> [Parse]
parseClueText ws
  = [ (d, l, t) | (d, l, wp) <- split3M ws
                , unwords l `elem` linkWords
                , (not . null . synonyms . unwords) d
                , t <- parseWordplay wp ]

solve :: Clue -> [Solution]
solve c@(ws, n)
  = [ (c, p, s) | p <- parseClue c 
                , s <- evaluate p n]

--   = [ (c, p, head (evaluate p n))) | p <- parseClue c 
--                                    , not (null (evaluate p n))]


------------------------------------------------------
-- Some additional test functions

-- Returns the solution(s) to the first k clues.
-- The nub removes duplicate solutions arising from the
-- charade parsing rule.
solveAll :: Int -> [[String]]
solveAll k
  = map (nub . map getSol . solve . (clues !!)) [0..k-1]

getSol :: Solution -> String
getSol (_, _, sol) = sol

showAll
  = mapM_ (showSolutions . solve . (clues !!)) [0..23]

