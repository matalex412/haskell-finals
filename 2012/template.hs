import Data.List
import Data.Maybe

type Id = String

type State = Int

type Transition = ((State, State), Id)

type LTS = [Transition]

type Alphabet = [Id]

data Process = STOP | Ref Id | Prefix Id Process | Choice [Process] 
             deriving (Eq, Show)

type ProcessDef = (Id, Process)

type StateMap = [((State, State), State)]

------------------------------------------------------
-- PART I

lookUp :: Eq a => a -> [(a, b)] -> b
--Pre: The item is in the table
lookUp x
  = fromJust . lookup x

states :: LTS -> [State]
states
  = sort . nub . concatMap (\((s, s'), _) -> [s, s'])

transitions :: State -> LTS -> [Transition]
transitions s
  = filter ((== s) . fst . fst)

alphabet :: LTS -> Alphabet
alphabet 
  = nub . map snd

------------------------------------------------------
-- PART II

actions :: Process -> [Id]
actions (Prefix id p)
  = nub (id : actions p)
actions (Choice ps)
  = nub (concatMap actions ps)
actions _
  = []


accepts :: [Id] -> [ProcessDef] -> Bool
--Pre: The first item in the list of process definitions is
--     that of the start process.
accepts ids pDefs@((_, startP) :  _)
  = accepts' ids startP
  where
    accepts' [] _
      = True
    accepts' _ STOP
      = False
    accepts' ids (Ref pName)
      = accepts' ids (lookUp pName pDefs)
    accepts' (id : ids) (Prefix id' p)
      = id == id' && accepts' ids p
    accepts' ids (Choice ps)
      = any (accepts' ids) ps
accepts _ _
  = False



------------------------------------------------------
-- PART III


composeTransitions :: Transition -> Transition 
                  -> Alphabet -> Alphabet 
                  -> StateMap 
                  -> [Transition]
--Pre: The first alphabet is that of the LTS from which the first transition is
--     drawn; likewise the second.
--Pre: All (four) pairs of source and target states drawn from the two transitions
--     are contained in the given StateMap.
composeTransitions ((s, t), a) ((s', t'), a') alpha alpha' m
  | a == a' 
      = [ ((ss', tt'), a) ]
  | a `elem` alpha', a' `elem` alpha
      = [] 
  | a' `elem` alpha
      = [ ((ss', ts'), a) ]
  | a `elem` alpha'
      = [ ((ss', st'), a') ]
  | otherwise
      = [ ((ss', ts'), a), ((ss', st'), a') ]
  where
    tt' = lookUp (t, t') m
    ss' = lookUp (s, s') m
    ts' = lookUp (t, s') m
    st' = lookUp (s, t') m

pruneTransitions :: [Transition] -> LTS
pruneTransitions ts
  = nub (visit 0 [])
  where
    visit :: State -> [State] -> [Transition]
    visit s visited 
      | s `notElem` visited
          = concatMap (flip visit (s : visited)) (states outgoing) ++ outgoing
      | otherwise
          = []
      where
        outgoing = transitions s ts

------------------------------------------------------
-- PART IV


-- compose :: LTS -> LTS -> LTS
-- compose lts lts'
--   = (pruneTransitions . concat) newLts
--   where
--     statePairs = [ (s, s') | s <- states lts, s' <- states lts' ]
--     m          = zip statePairs [0..]
--     alpha      = alphabet lts
--     alpha'     = alphabet lts'

--     newLts =  [ let a = if null ts' then "$'" : alpha else alpha; 
--                       a' = if null ts then "$" : alpha' else alpha' 
--                   in  composeTransitions t t' a a' m
--                 | (s, s') <- statePairs
--                 , ts <- [transitions s lts]
--                 , ts' <- [transitions s' lts']
--                 , t <- if null ts then [((s, s), "$")] else ts
--                 , t' <- if null ts' then [((s', s'), "$'")] else ts']

compose :: LTS -> LTS -> LTS
compose lts lts'
  = (pruneTransitions . concat) newLts
  where
    statePairs = [ (s, s') | s <- states lts, s' <- states lts' ]
    m          = zip statePairs [0..]
    alpha      = "$'" : alphabet lts
    alpha'     = "$" : alphabet lts'

    newLts =  [ composeTransitions t t' alpha alpha' m
                | (s, s') <- statePairs
                , t       <- ((s, s), "$") : transitions s lts
                , t'      <- ((s', s'), "$'") : transitions s' lts' ]


------------------------------------------------------
-- PART V

buildLTS :: [ProcessDef] -> LTS
-- Pre: All process references (Ref constructor) have a corresponding
--      definition in the list of ProcessDefs.
buildLTS 
  = undefined

------------------------------------------------------
-- Sample process definitions...

vendor, clock, play, maker, user, p, q, switch, off, on :: ProcessDef

vendor 
  = ("VENDOR", Choice [Prefix "red"  (Prefix "coffee" (Ref "VENDOR")),
                       Prefix "blue" (Prefix "tea" (Ref "VENDOR")),
                       Prefix "off" STOP])

clock 
  = ("CLOCK", Prefix "tick" (Prefix "tock" (Ref "CLOCK")))

play 
  = ("PLAY", Choice [Prefix "think" (Prefix "move" (Ref "PLAY")), 
                     Prefix "end" STOP])

maker 
  = ("MAKER", Prefix "make" (Prefix "ready" (Ref "MAKER")))

user  
  = ("USER",  Prefix "ready" (Prefix "use" (Ref "USER")))

p = ("P", Prefix "a" (Prefix "b" (Prefix "c" STOP)))

q = ("Q",  Prefix "d" (Prefix "c" (Prefix "b" (Ref "Q"))))

switch 
  = ("SWITCH", Ref "OFF")

off 
  = ("OFF", Choice [Prefix "on" (Ref "ON")])

on  
  = ("ON",  Choice [Prefix "off" (Ref "OFF")])

------------------------------------------------------
-- Sample LTSs...

vendorLTS, clockLTS, playLTS, clockPlayLTS, makerLTS, userLTS, makerUserLTS, 
  pLTS, qLTS, pqLTS, switchLTS :: LTS

vendorLTS 
  = [((0,1),"off"),((0,2),"blue"),((0,3),"red"),((2,0),"tea"),((3,0),"coffee")]

clockLTS 
  = [((0,1),"tick"),((1,0),"tock")]

playLTS 
  = [((0,1),"end"),((0,2),"think"),((2,0),"move")]

clockPlayLTS 
  = [((0,1),"end"),((1,4),"tick"),((4,1),"tock"),((0,3),"tick"),
     ((3,4),"end"),((3,0),"tock"),((3,5),"think"),((5,3),"move"),
     ((5,2),"tock"),((2,0),"move"),((2,5),"tick"),((0,2),"think")]

makerLTS 
  = [((0,1),"make"),((1,0),"ready")]

userLTS 
  = [((0,1),"ready"),((1,0),"use")]

makerUserLTS 
  = [((0,2),"make"),((2,1),"ready"),((1,0),"use"),((1,3),"make"),((3,2),"use")]

pLTS 
  = [((0,1),"a"),((1,2),"b"),((2,3),"c")]

qLTS 
  = [((0,1),"d"),((1,2),"c"),((2,0),"b")]

pqLTS 
  = [((0,1),"d"),((1,4),"a"),((0,3),"a"),((3,4),"d")]

switchLTS 
  = [((0,1),"on"),((1,0),"off")]
