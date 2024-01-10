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
lookUp k
  = fromJust . lookup k

states :: LTS -> [State]
states
  = nub . concatMap (\((s, t), _) -> [s, t])

transitions :: State -> LTS -> [Transition]
transitions s
  = filter (\((s', _), _) -> s == s')

alphabet :: LTS -> Alphabet
alphabet
  = nub . map snd

------------------------------------------------------
-- PART II

actions :: Process -> [Id]
actions
  = nub . actions'
  where
    actions' (Prefix act p)
      = act : actions' p
    actions' (Choice ps)
      = concatMap actions' ps
    actions' _
      = []


accepts :: [Id] -> [ProcessDef] -> Bool
--Pre: The first item in the list of process definitions is
--     that of the start process.
accepts acts pDefs@((startS, startP) : _)
  = accepts' acts startP
  where
    accepts' :: [Id] -> Process -> Bool
    accepts' [] _
      = True
    accepts' _ STOP
      = False
    accepts' acts (Ref id)
      = accepts' acts (lookUp id pDefs)
    accepts' (act : acts) (Prefix act' p)
      = act == act' && accepts' acts p
    accepts' acts (Choice ps)
      = any (accepts' acts) ps
        

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
composeTransitions ((s, t), a) ((s', t'), a') alp1 alp2 m
  | a == a'                       = [((ss', tt'), a)]
  | a `elem` alp2, a' `elem` alp1 = []
  | a' `elem` alp1                = [((ss', ts'), a)]
  | a `elem` alp2                 = [((ss', st'), a')]
  | otherwise                     = [((ss', ts'), a), ((ss', st'), a')]
  where
    ss' = lookUp (s, s') m
    tt' = lookUp (t, t') m
    ts' = lookUp (t, s') m
    st' = lookUp (s, t') m


pruneTransitions :: [Transition] -> LTS
pruneTransitions ts
  = visit 0 []
  where
    visit :: State -> [State] -> [Transition]
    visit s ss 
      | s `notElem` ss = fromS ++ concatMap (`visit` (s : ss)) tos
      | otherwise      = []
      where
        fromS = transitions s ts
        tos   = map (snd . fst) fromS
------------------------------------------------------
-- PART IV

compose :: LTS -> LTS -> LTS
compose lts1 lts2
  = pruneTransitions lts
  where
    alp1 = alphabet lts1
    alp2 = alphabet lts2

    ss = sort (states lts1)
    ss' = sort (states lts2)

    sss = [ (s, s') | s <- ss, s' <- ss' ]
    m = zip sss [0..]

    lts = (nub . concat) [ composeTransitions t t' ("$'" : alp1) ("$" : alp2) m 
                 | (s, s') <- sss
                 , t <- ((s, s'), "$") : transitions s lts1
                 , t' <-((s', s), "$'") : transitions s' lts2 ]


------------------------------------------------------
-- PART V

-- data Process = STOP | Ref Id | Prefix Id Process | Choice [Process] 
--              deriving (Eq, Show)

-- type ProcessDef = (Id, Process)

buildLTS :: [ProcessDef] -> LTS
-- Pre: All process references (Ref constructor) have a corresponding
--      definition in the list of ProcessDefs.
buildLTS pDefs@((_, startP) : _)
  = lts 
  where
    (lts, _, _) = (helper [] startP 0 1)

    helper :: [Process] -> Process -> State -> State -> (LTS, State, [Process])
    helper m p c _ | p `elem` m
      = ([], c, m)
    helper m p@(Ref id') c n
      =  helper (p : m) (lookUp id' pDefs) c n
    helper m (STOP) c n
      = ([], c, m)
    helper m p@(Prefix act p') c n
      | otherwise = (((c, n), act) : lts', n', m')
      where
        (lts', n', m') = helper (p : m) p' n (n + 1)
    helper m (Choice (x : xs)) c n
      = (lts ++ lts', n'', m'')
      where
        (lts, n', m') = helper m x c n
        (lts', n'', m'') = helper m' (Choice xs) c n'
    helper m (Choice []) c n
      = ([], n, m)

-- 0 1
-- 1 2
-- 2 3
-- = (2)
-- ((0,1), "red") : ((1,2), "coffee") : ()

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
