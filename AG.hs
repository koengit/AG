module Main where

--------------------------------------------------------------------------------

import Data.Char
import Data.List
import Data.Maybe
import qualified Data.IntMap as M
import qualified Data.Set as S
import System.Environment
import System.IO
import qualified Data.PSQueue as Q

--------------------------------------------------------------------------------

import MiniSat

--------------------------------------------------------------------------------

type Name
  = String

type Attr
  = Int

--------------------------------------------------------------------------------

data Type
  = Type Name [Rule]
 deriving ( Eq, Ord, Show )

data Rule
  = Rule Name [Field]
 deriving ( Eq, Ord, Show )

data Field
  = Field Name Name [Attr] [Attr] [(Attr,Attr)]
 deriving ( Eq, Ord, Show )

--------------------------------------------------------------------------------

ntAttrs :: Type -> (Name, [Attr], [Attr])
ntAttrs (Type tp rs) = (tp, [0..n-1], [n..n+m-1])
 where
  Rule _ fs : _  = rs
  (ins,outs) : _ = [ (ins,outs) | Field "lhs" _ ins outs _ <- fs ]
  n = length ins
  m = length outs

typeField :: Field -> Name
typeField (Field _ tp _ _ _) = tp

insOuts :: [Type] -> Name -> [(Attr,Attr)]
insOuts ts tp = S.toList $ S.fromList
  [ (i,j)
  | Type _ rs <- ts
  , Rule _ fs <- rs
  , let pointsTo   = S.fromList
                   [ y
                   | Field _ _ _ _ deps <- fs
                   , (_,y) <- deps
                   ]
        pointsFrom = S.fromList
                   [ x
                   | Field _ _ _ _ deps <- fs
                   , (x,_) <- deps
                   ]
  , Field fld tp' ins' outs' _ <- fs
  , tp == tp'
  , let (ins,outs) | fld == "lhs" = (ins',outs')
                   | otherwise    = (outs',ins')
  , (x,i) <- ins `zip` [0..]
  , x `S.member` pointsFrom
  , (y,j) <- outs `zip` [length ins..]
  , y `S.member` pointsTo
  ]

--------------------------------------------------------------------------------

parse :: String -> [Type]
parse s = pTypes (lines s)
 where
  clean = unwords . words
  
  pTypes (tp : ls) | any (not . isSpace) tp = Type (clean tp) rs : ts
   where
    (rs, ls') = pRules ls
    ts        = pTypes ls'

  pTypes (_:ls) = pTypes ls
  pTypes []     = []

  pRules ((' ':cn) : ls) = (Rule (clean cn) fs : rs, ls'')
   where
    (fs, ls')  = pFields ls
    (rs, ls'') = pRules ls'

  pRules ls = ([], ls)
  
  pFields (fld : ins : outs : ls) | "::" `elem` ws =
    (Field fl tp (commas ins) (commas outs) [ (read a,read b) | [a, "-->", b] <- map words arrows ] : fs, ls'')
   where
    ws             = words fld
    [fl, "::", tp] = ws
    (arrows, ls')  = splitWhile (("-->" `elem`) . words) ls
    (fs, ls'')     = pFields ls'
    commas         = map read . words . map (\c -> if c == ',' then ' ' else c) . drop 1 . dropWhile (/=':')

  pFields ls = ([], ls)

splitWhile :: (a -> Bool) -> [a] -> ([a],[a])
splitWhile p [] = ([],[])
splitWhile p (x:xs)
  | p x       = (x:as,bs)
  | otherwise = ([],x:xs)
 where
  (as,bs) = splitWhile p xs

--------------------------------------------------------------------------------

type Node  = Int
type Map b = M.IntMap b

--------------------------------------------------------------------------------

data Color = Blue | Green
 deriving ( Eq, Ord, Show )

type Edge  = (Node,Node,Lit,Color)

type Neigh = (Node,Lit,Color)

type Graph = Map [Neigh]

mkGraph :: Solver -> [Edge] -> IO Graph
mkGraph sat tups =
  do tups' <- smashEdges sat tups
     return $ M.fromListWith (++) $ concat $
       [ [(a, [(b,e,c)]), (b, [(a,neg e,c)])]
       | (a,b,e,c) <- tups'
       ]

smashEdges :: Solver -> [Edge] -> IO [Edge]
smashEdges sat = sequence . map smash . groupBy nodes . sort . map norm
 where
  norm (a,b,e,c) | a <= b    = (a,b,e,c)
                 | otherwise = (b,a,neg e,c)

  (a1,b1,_,_) `nodes` (a2,b2,_,_) = (a1,b1) == (a2,b2)
  
  smash [t] =
    do return t

  smash ((a,b,e1,c1):(_,_,e2,c2):ts) =
    do e <- smashEdge e1 e2
       smash ((a,b,e,smashColor c1 c2):ts)
  
  smashEdge e1 e2 =
    do addClause sat [neg e1, e2]
       addClause sat [e1, neg e2]
       return e1

  -- what happens when we return Blue here?
  smashColor Green _ = Green
  smashColor _ Green = Green
  smashColor _ _     = Blue

add :: Edge -> Graph -> Graph
add (a,b,e,c) = M.adjust (((b,e,c):))     a
              . M.adjust (((a,neg e,c):)) b

--------------------------------------------------------------------------------

-- rules:
-- 1. No edges from a node to itself i.e. (x,x,_,_)
-- 2. we never have to consider cycles with two or more adjacent green edges
-- 3. new edges are always blue

noCycles :: Solver -> Graph -> IO ()
noCycles sat graph =
  removeSimplicial sat graph (Q.fromList [ a Q.:-> weight xs | (a,xs) <- M.toList graph ])

type Queue = Q.PSQ Node Int

removeSimplicial :: Solver -> Graph -> Queue -> IO ()
removeSimplicial sat graph queue | M.null graph =
  do return ()

removeSimplicial sat graph queue =
  do news <- sequence [ triangle sat graph p q | (p,q) <- bluePairs neighs ]
     let graph' = foldr add (foldr (M.adjust remNode) (M.delete node graph) bs) (concat news)
     removeSimplicial sat graph' (foldr (uncurry Q.insert) queue' [ (b, weigh b graph') | b <- bs ])
 where
  Just ((node Q.:-> _),queue') = Q.minView queue
  Just neighs       = M.lookup node graph
  bs                = [ b | (b,_,_) <- neighs ]
  remNode bs        = [ b | b@(a,_,_) <- bs, a /= node ]
  weigh a           = weight . fromJust . M.lookup a

bluePairs :: [Neigh] -> [(Neigh,Neigh)]
bluePairs as = [ (p,q) | p <- greens, q <- blues ] ++ pairs blues
 where
  greens = [ a | a@(_,_,Green) <- as ]
  blues  = [ a | a@(_,_,Blue)  <- as ]

weight :: [Neigh] -> Int
weight xs = g * b + b * b
 where
  g = length [ x | x@(_,_,Green) <- xs ]
  b = length [ x | x@(_,_,Blue) <- xs ]

triangle :: Solver -> Graph -> Neigh -> Neigh -> IO [Edge]
triangle sat graph (a,ea,ca) (b,eb,cb) =
  case M.lookup a graph of
    Just as ->
      case [ (e,c) | (a',e,c) <- as, a' == b ] of
        [] ->
          do ab <- newLit sat
             addTriangle ea eb ab
             return [(a,b,ab,Blue)]
           
        [(ab,c)] ->
          do if c == Blue || (ca == Blue && cb == Blue)
               then addTriangle ea eb ab
               else return ()
             return []
 where
  addTriangle ea eb ab =
    do addClause sat [ea,ab,neg eb]     -- one must point n -> a -> b -> n
       addClause sat [neg ea,neg ab,eb] -- one must point n <- a <- b <- n
       return ()

pairs :: [a] -> [(a,a)]
pairs []     = []
pairs (x:xs) = [ (x,y) | y <- xs ] ++ pairs xs

--------------------------------------------------------------------------------

main :: IO ()
main =
  do [file] <- getArgs
     s <- readFile file
     let ts  = parse s
         nts = map ntAttrs ts
     
     sat <- newSolver
     ntgs <- constraintsNonTerminals sat ts nts
     constraintsProductions sat ts nts ntgs

     putStrLn "-- SOLVING --"
     nv <- minisat_num_vars sat
     nc <- minisat_num_clauses sat
     putStrLn ("have " ++ show nv ++ " vars, " ++ show nc ++ " clauses")
     b <- solve sat []
     print b

constraintsNonTerminals :: Solver -> [Type] -> [(Name,[Attr],[Attr])] -> IO [(Name,[(Attr,Attr,Lit)])]
constraintsNonTerminals sat ts nts =
  do putStrLn "-- Non-Terminals --"
     sequence
       [ do putStr ("data " ++ tp ++ " ... ")
            hFlush stdout
            es <- sequence [ do l <- newLit sat
                                return (a,b,l)
                           | (a,b) <- insOuts ts tp
                           ]
            g <- mkGraph sat [ (a, b, e, Blue) | (a, b, e) <- es ]
            noCycles sat g
            putStrLn (show (length es) ++ " edges")
            return (tp, es)
       | t <- ts
       , let (tp, ins, outs) = ntAttrs t
       ]

constraintsProductions :: Solver -> [Type] -> [(Name,[Attr],[Attr])] -> [(Name,[(Attr,Attr,Lit)])] -> IO ()
constraintsProductions sat ts nts ntgs =
  do putStrLn "-- Productions --"
     true <- newLit sat
     addClause sat [true]
     sequence_
       [ do putStr (r ++ " :: " ++ argType fs ++ tp ++ " ... ")
            hFlush stdout
            g <- mkGraph sat graph
            noCycles sat g
            putStrLn (show (M.size g) ++ " nodes")
       | Type tp rs <- ts
       , Rule r fs <- rs
       , let graph = concat
                     [ -- edges from production rule
                       [ (a, b, true, Blue)
                       | (a,b) <- deps
                       , assert "self-loop" (a /= b)
                       ]
                       -- edges from non-terminal
                    ++ [ (inn a, out b, e, Green)
                       | (a, b, e) <- es
                       ]
                     | Field fld tp ins outs deps <- fs
                     , let (ins',outs') | fld == "lhs" = (ins,outs)
                                        | otherwise    = (outs,ins)
                      
                           (ins0,outs0) = head [ (ins,outs) | (tp',ins,outs) <- nts, tp == tp' ]
                           es           = head [ es | (tp',es) <- ntgs, tp == tp' ]
                           inn a        = head [ a' | (a0,a') <- ins0 `zip` ins', a == a0 ]
                           out b        = head [ b' | (b0,b') <- outs0 `zip` outs', b == b0 ]

                     , assert (r ++ "::" ++ tp ++ ".ins") (length ins' == length ins0)
                     , assert (r ++ "::" ++ tp ++ ".outs") (length outs' == length outs0)
                     ]
       ]
 where
  argType []  = ""
  argType [f] = typeField f ++ " -> "
  argType fs  = "(" ++ concat (intersperse ", " (map typeField fs)) ++ ") -> "

--------------------------------------------------------------------------------

assert :: String -> Bool -> Bool
assert s True  = True
assert s False = error s

