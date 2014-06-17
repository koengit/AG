module Main where

--------------------------------------------------------------------------------

import Data.Char
import Data.List
import Data.Maybe
import qualified Data.IntMap as M
import qualified Data.Set as S
import System.Environment
import System.Exit
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

type Graph = Map (Map Lit, Map Lit) -- (green,blue)

mkGraph :: Solver -> [Edge] -> IO Graph
mkGraph sat tups =
  do tups' <- smashEdges sat tups
     let greens = [ [(a, (M.singleton b e,M.empty)), 
                     (b, (M.singleton a (neg e),M.empty))]
                  | (a,b,e,Green) <- tups'
                  ]
     let blues = [ [(a, (M.empty, M.singleton b e)),
                     (b, (M.empty, M.singleton a (neg e)))]
                  | (a,b,e,Blue) <- tups'
                  ]
     return $ M.fromListWith comb $ concat $ blues ++ greens
       where comb (g1,b1) (g2,b2) = (g1 `M.union` g2, b1 `M.union` b2)

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


remNode :: Node -> Graph -> Graph
remNode node g = M.map (\(g,b) -> (M.delete node g, M.delete node b)) $ 
                 M.delete node g

addBlue :: Node -> Node -> Lit -> Graph -> Graph
addBlue a b e = single a b e . single b a (neg e) where
  single :: Node -> Node -> Lit -> Graph -> Graph
  single a b e = M.adjustWithKey (\_ (mg,mb) -> (mg, M.insert b e mb)) a

--------------------------------------------------------------------------------

-- rules:
-- 1. No edges from a node to itself i.e. (x,x,_,_)
-- 2. we never have to consider cycles with two or more adjacent green edges
-- 3. new edges are always blue

noCycles :: Solver -> Graph -> IO ()
noCycles sat graph | M.null graph =
  do return ()
noCycles sat graph =
  do g' <- foldM (\g (p,q) -> triangle sat p q g) graph (bluePairs neighs)
     noCycles sat (remNode node g')
 where
   node        = snd $ minimum [ (weight xs, a) | (a,xs) <- M.toList graph ]
   Just neighs = M.lookup node graph

bluePairs :: (Map Lit, Map Lit) -> [(Neigh,Neigh)]
bluePairs (mg,mb) = [ (p,q) | p <- greens, q <- blues ] ++ pairs blues
 where
  greens = [ (n,l,Green) | (n,l) <- M.toList mg ]
  blues  = [ (n,l,Blue)  | (n,l) <- M.toList mb ]


weight :: (Map Lit, Map Lit) -> Int
weight (mg,mb) = g * b + b * b
 where
  g = M.size mg
  b = M.size mb

triangle :: Solver -> Neigh -> Neigh -> Graph -> IO Graph
triangle sat (a,ea,ca) (b,eb,cb) graph =
  case M.lookup a graph of
    Just (mg,mb) ->
      case M.lookup b mg of -- green edge
        Just ab -> if ca == Blue && cb == Blue
                   then addTriangle ea eb ab
                   else return graph
        Nothing -> case M.lookup b mb of -- blue edge
          Nothing ->
            do ab <- newLit sat
               addTriangle ea eb ab
               return $ addBlue a b ab graph
          Just ab -> addTriangle ea eb ab
 where
  addTriangle ea eb ab =
    do addClause sat [ea,ab,neg eb]     -- one must point n -> a -> b -> n
       addClause sat [neg ea,neg ab,eb] -- one must point n <- a <- b <- n
       return graph


pairs :: [a] -> [(a,a)]
pairs []     = []
pairs (x:xs) = [ (x,y) | y <- xs ] ++ pairs xs

--------------------------------------------------------------------------------

type Args = (FilePath, Maybe (Name, Attr))

parseArgs :: IO Args
parseArgs =
  do as <- getArgs
     case as of
       [file]                            -> return (file, Nothing)
       [file,tp,attr] | all isDigit attr -> return (file, Just (tp, read attr))
       _                                 -> do putStr $ unlines
                                                 [ "Usage: AG <file>"
                                                 , "   or: AG <file> <type> <attr>"
                                                 ]
                                               exitWith (ExitFailure 1)

main :: IO ()
main =
  do (file, mobj) <- parseArgs
     s <- readFile file
     let ts  = parse s
         nts = map ntAttrs ts
     
     sat <- newSolver
     eliminate sat True -- switch off simplification
     ntgs <- constraintsNonTerminals sat ts nts
     constraintsProductions sat ts nts ntgs

     putStrLn "-- SOLVING --"
     nv <- minisat_num_vars sat
     nc <- minisat_num_clauses sat
     putStrLn ("have " ++ show nv ++ " vars, " ++ show nc ++ " clauses")
     b <- solve sat []
     solveStats sat
     if b then
       do putStrLn "++ SOLUTION FOUND ++"
          numbs <- sequence [ visitsNonTerminal sat 50 edges | (_,edges) <- ntgs ]
          total@(N xs _) <- plusList sat numbs
          let show2 x | x < 10    = " " ++ show x
                      | otherwise = show x
          
              opti mayn =
                do b <- solve sat [total .<= n | Just n <- [mayn]]
                   if b then
                     do sequence_ [ addClause sat [total .<= n] | Just n <- [mayn]]
                        as <- sequence [ modelNumber sat n | n <- numbs ]
                        putStrLn ( unwords (map (show2 . (+1)) as)
                                ++ "  = " ++ show (sum as + length as)
                                ++ case mayn of
                                     Nothing -> ""
                                     Just n  -> " (<= " ++ show (n+length as) ++ "?)"
                                 )
                        opti (Just (sum as - 1))
                    else
                     do putStrLn "(sum is optimal)"
          opti Nothing
          --solve sat []
          as <- sequence [ modelNumber sat n | n <- numbs ]
          let mopti [] =
                do putStrLn "(maxima are optimal)"
          
              mopti nas =
                do b <- solve sat ( numb .<= (a-1)
                                  : [ numb .<= a | numb <- tail mnumbs ]
                                 ++ [ numb .<= (a-1) | (numb,_) <- inumbs ]
                                  )
                   if b then
                     do as <- sequence [ modelNumber sat num | num <- numbs ]
                        putStrLn ( unwords (map (show2 . (+1)) as)
                                ++ "  = " ++ show (sum as + length as)
                                 )
                        nas' <- sequence [ do a <- modelNumber sat num
                                              return (num,a)
                                         | (num,_) <- nas
                                         ]
                        mopti nas'
                    else
                     do addClause sat [ numb .<= a ]
                        mopti ( [ (numb,a) | numb <- tail mnumbs ] ++ inumbs )
                where
                 a       = maximum (map snd nas)
                 mnumbs  = [ num | (num,a') <- nas, a == a' ]
                 numb    = head mnumbs
                 inumbs  = [ (num,a') | (num,a') <- nas, a' < a ]
               
              (x,_) `first2` (y,_) = x `compare` y
          
          mopti [ (numb, a) | (numb,a) <- numbs `zip` as ]
      else
       do putStrLn "** NO SOLUTION FOUND **"


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

visitsNonTerminal :: Solver -> Int -> [(Attr,Attr,Lit)] -> IO Number
visitsNonTerminal sat n edges =
  do -- create all numbers
     numbs <- sequence [ mkNumber sat n | _ <- attrs ]
     let table = attrs `zip` numbs
     
     -- add constraints about visits
     sequence_
       [ do leqOr sat [neg x] na nb
            ltOr  sat [x]     nb na
       | (a,b,x) <- edges
       , (a',na) <- table
       , a == a'
       , (b',nb) <- table
       , b == b'
       ]
     
     -- take the "maximum"
     maxi <- mkNumber sat n
     sequence_ [ leqOr sat [] numb maxi | numb <- numbs ]
     return maxi
 where
  attrs = nub [ c | (a,b,_) <- edges, c <- [a,b] ]

--------------------------------------------------------------------------------

solveStats :: Solver -> IO ()
solveStats sat =
  do n <- minisat_num_assigns sat
     m <- minisat_num_conflicts sat
     putStrLn ("assigns: " ++ show n ++ ", conflicts: " ++ show m)

--------------------------------------------------------------------------------

data Number = N [Lit] Lit

mkNumber :: Solver -> Int -> IO Number
mkNumber sat k =
  do tr <- newLit sat
     addClause sat [tr]
     xs <- sequence [ newLit sat | _ <- [1..k] ]
     sequence_ [ addClause sat [neg a, b] | (a,b) <- xs `zip` drop 1 xs ]
     return (N xs tr) 

leqOr :: Solver -> [Lit] -> Number -> Number -> IO ()
leqOr sat pre (N xs _) (N ys _) = leq (reverse xs) (reverse ys)
 where
  leq (x:xs) (y:ys) =
    do addClause sat (pre ++ [neg x, y])
       leq xs ys
  
  leq (x:xs) [] =
    do addClause sat (pre ++ [neg x])
       leq xs []
  
  leq [] _ =
    do return ()

ltOr :: Solver -> [Lit] -> Number -> Number -> IO ()
ltOr sat pre a b = leqOr sat pre (plus1 a) b

plus1 :: Number -> Number
plus1 (N xs tr) = N (xs ++ [tr]) tr

plus :: Solver -> Number -> Number -> IO Number
plus sat (N xs tr) (N ys _) =
  do zs <- map fromJust `fmap` merge sat (map Just xs) (map Just ys)
     return (N zs tr)

plusList :: Solver -> [Number] -> IO Number
plusList sat as = go (sortBy first [ (length xs, a) | a@(N xs _) <- as ])
 where
  go [] =
    do mkNumber sat 0
  
  go [(_,a)] =
    do return a
  
  go ((n,a):(m,b):as) =
    do c <- plus sat a b
       go (insertBy first (n+m,c) as)

  (x,_) `first` (y,_) = x `compare` y

--------------------------------------------------------------------------------

(.<=), (.>=) :: Number -> Int -> Lit
N xs true .<= k | length xs <= k = true
                | k < 0          = neg true
                | otherwise      = neg (xs !! (length xs - 1 - k))

N xs true .>= k | length xs < k  = neg true
                | k <= 0         = true
                | otherwise      = xs !! (length xs - k)

--------------------------------------------------------------------------------

modelNumber :: Solver -> Number -> IO Int
modelNumber sat (N xs _) =
  do bs <- sequence [ modelValue sat x | x <- xs ]
     if sort bs /= bs then print bs else return ()
     return (length [ () | b <- bs, b /= Just False ])

--------------------------------------------------------------------------------

xsort :: Solver -> [Lit] -> IO [Lit]
xsort sat []  = do return []
xsort sat [x] = do return [x]
xsort sat xs  = do as <- xsort sat (take k xs)
                   bs <- xsort sat (drop k xs)
                   map fromJust `fmap` merge sat (map Just as) (map Just bs)
 where
  k = length xs `div` 2

merge2 :: Solver -> Maybe Lit -> Maybe Lit -> IO [Maybe Lit]
merge2 sat Nothing b = return [b, Nothing]
merge2 sat a Nothing = return [a, Nothing]
merge2 sat (Just x) (Just y) =
  do a <- newLit sat
     b <- newLit sat
     addClause sat [neg x, b]
     addClause sat [neg y, b]
     addClause sat [neg x, neg y, a]
     addClause sat [x, neg a]
     addClause sat [y, neg a]
     addClause sat [x, y, neg b]
     return [Just a,Just b]

merge :: Solver -> [Maybe Lit] -> [Maybe Lit] -> IO [Maybe Lit]
merge sat []  bs  = return bs
merge sat as  []  = return as
merge sat [a] [b] = merge2 sat a b
merge sat as  bs  = take (a+b) `fmap` merge' (as ++ xas) (bs ++ xbs)
 where
  a   = length as
  b   = length bs
  m   = a `max` b
  n   = if even m then m else m+1
  xas = replicate (n-a) Nothing
  xbs = replicate (n-b) Nothing

  -- pre: as and bs have the same, even length
  merge' as bs =
    do xs <- merge sat eas ebs
       ys <- merge sat oas obs
       let x:xys = weave xs ys
       xys' <- sequence [ merge2 sat a b | (a,b) <- pairs xys ]
       return (x : concat xys' ++ [last xys])
   where
    (eas,oas) = evenOdds as
    (ebs,obs) = evenOdds bs

  evenOdds []       = ([], [])
  evenOdds [x]      = ([x], [])
  evenOdds (x:y:xs) = (x:es,y:os)
   where
    (es,os) = evenOdds xs

  pairs (x:y:xs) = (x,y) : pairs xs
  pairs _        = []

  unpairs ((x,y):xys) = x : y : unpairs xys
  unpairs []          = []

  weave (x:xs) (y:ys) = x : y : weave xs ys
  weave xs     ys     = xs ++ ys

--------------------------------------------------------------------------------

assert :: String -> Bool -> Bool
assert s True  = True
assert s False = error s
