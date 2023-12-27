{-# LANGUAGE ScopedTypeVariables #-}

import Data.Maybe
import Data.List
import Data.Ord (comparing)

type AttName = String

type AttValue = String

type Attribute = (AttName, [AttValue])

type Header = [Attribute]

type Row = [AttValue]

type DataSet = (Header, [Row])

data DecisionTree = Null |
                    Leaf AttValue | 
                    Node AttName [(AttValue, DecisionTree)]
                  deriving (Eq, Show)

type Partition = [(AttValue, DataSet)]

type AttSelector = DataSet -> Attribute -> Attribute

xlogx :: Double -> Double
xlogx p
  | p <= 1e-100 = 0.0
  | otherwise   = p * log2 p 
  where
    log2 x = log x / log 2

lookUp :: (Eq a, Show a, Show b) => a -> [(a, b)] -> b
lookUp x table
  = fromMaybe (error ("lookUp error - no binding for " ++ show x ++ 
                      " in table: " ++ show table))
              (lookup x table)

--------------------------------------------------------------------
-- PART I 50 mins
--------------------------------------------------------------------

allSame :: Eq a => [a] -> Bool
allSame xs
  = length (nub xs) <= 1

remove :: Eq a => a -> [(a, b)] -> [(a, b)]
remove x'
  = filter ((/= x') . fst)

lookUpAtt :: AttName -> Header -> Row -> AttValue
--Pre: attribute values unique to attribute?
--Pre: The attribute name is present in the given header.
lookUpAtt n h
  = head . filter (`elem` vs)
  where
    vs = lookUp n h

-- lookUp n . zip (map fst h)

removeAtt :: AttName -> Header -> Row -> Row
removeAtt n h
  = filter (`notElem` vs)
  where
    vs = lookUp n h

-- map snd . remove n . zip (map fst h)

-- addToMapping :: forall a b. Eq a => (a, b) -> [(a, [b])] -> [(a, [b])]
-- addToMapping (x, y) xyss
--   | x `notElem` map fst xyss = (x, [y]) : xyss
--   | otherwise                = map addExisting xyss
--   where
--     addExisting :: (a, [b]) -> (a, [b])
--     addExisting p@(x', ys') 
--       | x == x'   = (x', y : ys')
--       | otherwise = p


addToMapping :: Eq a => (a, b) -> [(a, [b])] -> [(a, [b])]
addToMapping (x, y) []
  = [(x, [y])]
addToMapping (x, y) (p@(x', ys) : xyss)
  | x == x'   = (x, y : ys) : xyss
  | otherwise = p : addToMapping (x, y) xyss


buildFrequencyTable :: Attribute -> DataSet -> [(AttValue, Int)]
--Pre: Each row of the data set contains an instance of the attribute
buildFrequencyTable (n, optns) (h, rs)
  = [ (optn, length (filter (==optn) vs)) | optn <- optns]
  where
    vs = map (lookUpAtt n h) rs

--------------------------------------------------------------------
-- PART II 15 mins
--------------------------------------------------------------------

nodes :: DecisionTree -> Int
nodes (Null)
  = 0
nodes (Leaf _)
  = 1
nodes (Node _ ots)
  = 1 + sum (map (nodes . snd) ots)

evalTree :: DecisionTree -> Header -> Row -> AttValue
evalTree Null _ _
  = ""
evalTree (Leaf v) _ _
  = v
evalTree (Node n ots) atts r
  = evalTree (lookUp (lookUpAtt n atts r) ots) atts r

--------------------------------------------------------------------
-- PART III
--------------------------------------------------------------------

--
-- Given...
-- In this simple case, the attribute selected is the first input attribute 
-- in the header. Note that the classifier attribute may appear in any column,
-- so we must exclude it as a candidate.
--
nextAtt :: AttSelector
--Pre: The header contains at least one input attribute
nextAtt (header, _) (classifierName, _)
  = head (filter ((/= classifierName) . fst) header)

partitionData :: DataSet -> Attribute -> Partition
partitionData (h, rs) (n, optns)
  = [ (v, (h', rs)) | (v, rs) <- vrss ]
  where
    vrss = foldr (\r -> addToMapping (lookUpAtt n h r, removeAtt n h r)) 
                 [ (v, []) | v <- optns ] rs
    h'   = remove n h

  -- = map selectRows optns
  -- where
  --   h' = remove n h
  --   selectRows :: AttValue -> (AttValue, DataSet)
  --   selectRows v
  --     = (v, (h', [ removeAtt n h r | r <- rs, lookUpAtt n h r == v]))

buildTree :: DataSet -> Attribute -> AttSelector -> DecisionTree 
buildTree (header, []) classifier f
  = Null
buildTree t@(header, rs) c@(cName, _) f
  | allSame cs = Leaf (head cs)
  | otherwise  = Node n [(v, buildTree t' c f) | (v, t') <- partitionData t att]
  where
    att@(n, _) = f t c 
    cs = map (lookUpAtt cName header) rs

--------------------------------------------------------------------
-- PART IV
--------------------------------------------------------------------

entropy :: DataSet -> Attribute -> Double
entropy (_, []) _
  = 0.0
entropy d@(_, table) a@(_, optns)
  = sum (map term optns)
  where
    l = length table
    freqs = buildFrequencyTable a d
    
    term :: AttValue -> Double
    term v 
      = negate (xlogx p)
      where
        p = fromIntegral (lookUp v freqs) / fromIntegral l  

gain :: DataSet -> Attribute -> Attribute -> Double
gain d@(_, table) p@(_, optns) c
  = edc - sum (map term optns)
  where
    edc = entropy d c

    partitions = partitionData d p
    freqs = buildFrequencyTable p d
    l = length table

    term :: AttValue -> Double
    term v 
      = prob * entropy (lookUp v partitions) c
      where
        prob = fromIntegral (lookUp v freqs) / fromIntegral l

bestGainAtt :: AttSelector
bestGainAtt d@(header, _) c@(cName, _)
  = maximumBy (comparing (\att -> gain d att c)) (remove cName header )
  -- = maximumBy (comparing (flip (gain d) c)) (remove cName header )

--------------------------------------------------------------------

outlook :: Attribute
outlook 
  = ("outlook", ["sunny", "overcast", "rainy"])

temp :: Attribute 
temp 
  = ("temp", ["hot", "mild", "cool"])

humidity :: Attribute 
humidity 
  = ("humidity", ["high", "normal"])

wind :: Attribute 
wind 
  = ("wind", ["windy", "calm"])

result :: Attribute 
result
  = ("result", ["good", "bad"])

fishingData :: DataSet
fishingData
  = (header, table)

header :: Header
table  :: [Row]
header 
  =  [outlook,    temp,   humidity, wind,    result] 
table 
  = [["sunny",    "hot",  "high",   "calm",  "bad" ],
     ["sunny",    "hot",  "high",   "windy", "bad" ],
     ["overcast", "hot",  "high",   "calm",  "good"],
     ["rainy",    "mild", "high",   "calm",  "good"],
     ["rainy",    "cool", "normal", "calm",  "good"],
     ["rainy",    "cool", "normal", "windy", "bad" ],
     ["overcast", "cool", "normal", "windy", "good"],
     ["sunny",    "mild", "high",   "calm",  "bad" ],
     ["sunny",    "cool", "normal", "calm",  "good"],
     ["rainy",    "mild", "normal", "calm",  "good"],
     ["sunny",    "mild", "normal", "windy", "good"],
     ["overcast", "mild", "high",   "windy", "good"],
     ["overcast", "hot",  "normal", "calm",  "good"],
     ["rainy",    "mild", "high",   "windy", "bad" ]]

--
-- This is the same as the above table, but with the result in the second 
-- column...
--
fishingData' :: DataSet
fishingData'
  = (header', table')

header' :: Header
table'  :: [Row]
header' 
  =  [outlook,    result, temp,   humidity, wind] 
table' 
  = [["sunny",    "bad",  "hot",  "high",   "calm"],
     ["sunny",    "bad",  "hot",  "high",   "windy"],
     ["overcast", "good", "hot",  "high",   "calm"],
     ["rainy",    "good", "mild", "high",   "calm"],
     ["rainy",    "good", "cool", "normal", "calm"],
     ["rainy",    "bad",  "cool", "normal", "windy"],
     ["overcast", "good", "cool", "normal", "windy"],
     ["sunny",    "bad",  "mild", "high",   "calm"],
     ["sunny",    "good", "cool", "normal", "calm"],
     ["rainy",    "good", "mild", "normal", "calm"],
     ["sunny",    "good", "mild", "normal", "windy"],
     ["overcast", "good", "mild", "high",   "windy"],
     ["overcast", "good", "hot",  "normal", "calm"],
     ["rainy",    "bad",  "mild", "high",   "windy"]]

fig1 :: DecisionTree
fig1
  = Node "outlook" 
         [("sunny", Node "temp" 
                         [("hot", Leaf "bad"),
                          ("mild",Node "humidity" 
                                       [("high",   Leaf "bad"),
                                        ("normal", Leaf "good")]),
                          ("cool", Leaf "good")]),
          ("overcast", Leaf "good"),
          ("rainy", Node "temp" 
                         [("hot", Null),
                          ("mild", Node "humidity" 
                                        [("high",Node "wind" 
                                                      [("windy",  Leaf "bad"),
                                                       ("calm", Leaf "good")]),
                                         ("normal", Leaf "good")]),
                          ("cool", Node "humidity" 
                                        [("high", Null),
                                         ("normal", Node "wind" 
                                                         [("windy",  Leaf "bad"),
                                                          ("calm", Leaf "good")])])])]

fig2 :: DecisionTree
fig2
  = Node "outlook" 
         [("sunny", Node "humidity" 
                         [("high", Leaf "bad"),
                          ("normal", Leaf "good")]),
          ("overcast", Leaf "good"),
          ("rainy", Node "wind" 
                         [("windy", Leaf "bad"),
                          ("calm", Leaf "good")])]


outlookPartition :: Partition
outlookPartition
  = [("sunny",   ([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["hot","high","calm","bad"],["hot","high","windy","bad"],
                   ["mild","high","calm","bad"],["cool","normal","calm","good"],
                   ["mild","normal","windy","good"]])),
     ("overcast",([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["hot","high","calm","good"],["cool","normal","windy","good"],
                   ["mild","high","windy","good"],["hot","normal","calm","good"]])),
     ("rainy",   ([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["mild","high","calm","good"],["cool","normal","calm","good"],
                   ["cool","normal","windy","bad"],["mild","normal","calm","good"],
                   ["mild","high","windy","bad"]]))]