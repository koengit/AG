module Main where

--------------------------------------------------------------------------------

import Data.Char
import Data.List
import Data.Maybe
import qualified Data.IntMap as M
import qualified Data.Set as S
import qualified Data.Array.IO as A
import System.Environment
import System.IO
import Control.Monad

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

type SGraph = A.IOArray Node (Map Lit)
type Graph = (SGraph, SGraph) -- (green, blue)

mkGraph :: Solver -> [Edge] -> IO Graph
mkGraph sat tups =
  do tups' <- smashEdges sat tups
     let nodes = concat [[a,b] | (a,b,_,_) <- tups' ]
         maxNode | null tups' = 0
                 | otherwise  = maximum nodes
         minNode | null tups' = 0
                 | otherwise  = minimum nodes
     green <- mkSGraph (minNode,maxNode) [ (a,b,e) | (a,b,e,Green) <- tups' ]
     blue  <- mkSGraph (minNode,maxNode) [ (a,b,e) | (a,b,e,Blue) <- tups' ]
     return $ (green, blue)
     where
       mkSGraph :: (Node,Node) -> [(Node, Node, Lit)] -> IO SGraph
       mkSGraph bound edges = do
         g <- A.newArray bound M.empty
         mapM_ (\(a,b,e) -> addEdge a b e g) edges
         return g

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

addEdge :: Node -> Node -> Lit -> SGraph -> IO ()
addEdge a b e g = single a b e >> single b a (neg e) where
  single :: Node -> Node -> Lit -> IO ()
  single a b e = modifyArray g a $! M.insert b e

remNode :: Node -> Graph -> IO ()
remNode node (gg,bg) = remNode' gg >> remNode' bg where
  remNode' :: SGraph -> IO ()
  remNode' g = do
    outedges <- A.readArray g node
    mapM_ (\n -> modifyArray g n $ M.delete node) $ M.keys outedges

graphKeys :: Graph -> IO [Node]
graphKeys (gg,_) = A.getBounds gg >>= return . A.range

-- Why is this not in some standard lib?
modifyArray :: (A.MArray a e m, A.Ix i) => a i e -> i -> (e -> e) -> m ()
modifyArray a i f = A.readArray a i >>= \v -> A.writeArray a i (f v)
--------------------------------------------------------------------------------

-- rules:
-- 1. No edges from a node to itself i.e. (x,x,_,_)
-- 2. we never have to consider cycles with two or more adjacent green edges
-- 3. new edges are always blue

noCycles :: Solver -> Graph -> IO ()
noCycles sat graph@(gg,bg) = graphKeys graph >>= noCycles' . S.fromList where
  noCycles' :: S.Set Node -> IO ()
  noCycles' nodes | S.null nodes = return ()
  noCycles' nodes =
    do wn <- mapM (\n -> weight graph n >>= \w -> return (w,n)) $ 
             S.toList nodes
       let node = snd $ minimum wn
       mg <- A.readArray gg node
       mb <- A.readArray bg node
       mapM_ (\(p,q) -> triangle sat p q graph) (bluePairs mg mb)
       remNode node graph
       noCycles' (S.delete node nodes)

bluePairs :: Map Lit -> Map Lit -> [(Neigh,Neigh)]
bluePairs mg mb = [ (p,q) | p <- greens, q <- blues ] ++ pairs blues
 where
  greens = [ (n,l,Green) | (n,l) <- M.toList mg ]
  blues  = [ (n,l,Blue)  | (n,l) <- M.toList mb ]

weight :: Graph -> Node -> IO Int
weight (gg,bg) node = do
  mg <- A.readArray gg node
  mb <- A.readArray bg node
  let g = M.size mg
      b = M.size mb
  return $ g * b + b * b

triangle :: Solver -> Neigh -> Neigh -> Graph -> IO ()
triangle sat (a,ea,ca) (b,eb,cb) (gg,bg) = do
  mg <- A.readArray gg a
  case M.lookup b mg of -- green edge        
    Just ab -> if ca == Blue && cb == Blue
               then addTriangle ea eb ab
               else return ()
    Nothing -> do
      mb <- A.readArray bg a
      case M.lookup b mb of -- blue edge
        Just ab -> addTriangle ea eb ab
        Nothing ->
          do ab <- newLit sat
             addTriangle ea eb ab
             addEdge a b ab (bg)
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
            ns <- graphKeys g
            noCycles sat g
            putStrLn (show (length ns) ++ " nodes")
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
