module Queue where

import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding ( null )

--------------------------------------------------------------------------------

data Queue a w = Q (M.Map a w) (S.Set (w,a))

fromList :: (Ord a, Ord w) => [(a,w)] -> Queue a w
fromList aws = Q m q
 where
  m = M.fromListWith min aws
  q = S.fromList [ (w,a) | (a,w) <- M.toList m ]

insert :: (Ord a, Ord w) => a -> w -> Queue a w -> Queue a w
insert a w (Q m q) = Q (M.insert a w m) (S.insert (w,a) q)

null :: Queue a w -> Bool
null (Q m _) = M.null m

minView :: (Ord a, Ord w) => Queue a w -> Maybe ((a,w),Queue a w)
minView (Q m q) = 
  case S.minView q of
    Nothing         -> Nothing
    Just ((w,a),q') ->
      case M.lookup a m of
        Just w' | w == w' -> Just ((a,w), Q (M.delete a m) q')
        _                 -> minView (Q m q')

--------------------------------------------------------------------------------

