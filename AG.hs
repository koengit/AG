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
      else
       do putStrLn "** NO SOLUTION FOUND **"


constraintsNonTerminals :: Solver -> [Type] -> [(Name,[Attr],[Attr])] -> IO [(Name,[(Attr,Attr,Lit)])]
constraintsNonTerminals sat ts nts =
  do putStrLn "-- Non-Terminals --"
     sequence
       [ do let ios       = insOuts ts tp
                maxVisits = length ins `min` length outs `min` 11
            putStrLn ("data " ++ tp ++ " ... max. " ++ show maxVisits ++ " visits")
            
            -- create edges
            es <- sequence [ do x <- newLit sat
                                return (a,b,x)
                           | (a,b) <- ios
                           ]
            
            -- create all numbers
            let attrs = nub [ c | (a,b) <- ios, c <- [a,b] ]
            numbs <- sequence [ mkNumber sat maxVisits | _ <- attrs ]
            let table = attrs `zip` numbs
            
            -- add constraints about visits
            sequence_
              [ do leqOr sat [neg x] na nb
                   ltOr  sat [x]     nb na
              | (a,b,x) <- es
              , (a',na) <- table
              , a == a'
              , (b',nb) <- table
              , b == b'
              ]
            
            -- return edges
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
       [ do putStrLn (r ++ " :: " ++ argType fs ++ tp ++ " ... max. " ++ show maxVisits ++ " visits")
            
            -- create all numbers
            let attrs = nub [ c | (a,b,_) <- graph, c <- [a,b] ]
            numbs <- sequence [ mkNumber sat maxVisits | _ <- attrs ]
            let table = attrs `zip` numbs
            
            -- add constraints about visits
            sequence_
              [ do ltOr sat [neg x] na nb
                   when (x /= true) $ ltOr sat [x] nb na
              | (a,b,x) <- graph
              , (a',na) <- table
              , a == a'
              , (b',nb) <- table
              , b == b'
              ]
       | Type tp rs <- ts
       , Rule r fs <- rs
       , let maxVisits = sum [ length ins `min` length outs | Field fld tp ins outs deps <- fs ]
       
             graph = concat
                     [ -- edges from production rule
                       [ (a, b, true)
                       | (a,b) <- deps
                       , assert "self-loop" (a /= b)
                       ]
                       -- edges from non-terminal
                    ++ [ (inn a, out b, e)
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
