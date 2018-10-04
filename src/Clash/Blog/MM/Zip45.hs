module Clash.Blog.MM.Zip45 where

import Clash.Prelude

-- Has been added in development version of Clash

zipWith4
  :: (a -> b -> c -> d -> e)
  -> Vec n a
  -> Vec n b
  -> Vec n c
  -> Vec n d
  -> Vec n e
zipWith4 f us vs ws xs =
  zipWith
    (\(a, b) (c, d) -> f a b c d)
    (zip us vs)
    (zip ws xs)

zipWith5
  :: (a -> b -> c -> d -> e -> f)
  -> Vec n a
  -> Vec n b
  -> Vec n c
  -> Vec n d
  -> Vec n e
  -> Vec n f
zipWith5 f us vs ws xs ys =
  zipWith (\a (b,c,d,e) -> f a b c d e) us (zip4 vs ws xs ys)

zip4
  :: Vec n a
  -> Vec n b
  -> Vec n c
  -> Vec n d
  -> Vec n (a,b,c,d)
zip4 =
  zipWith4 (,,,)

zip5
  :: Vec n a
  -> Vec n b
  -> Vec n c
  -> Vec n d
  -> Vec n e
  -> Vec n (a,b,c,d,e)
zip5 = zipWith5 (,,,,)

unzip4
  :: Vec n (a,b,c,d)
  -> (Vec n a, Vec n b, Vec n c, Vec n d)
unzip4 xs =
  ( map (\(w,_,_,_) -> w) xs
  , map (\(_,x,_,_) -> x) xs
  , map (\(_,_,y,_) -> y) xs
  , map (\(_,_,_,z) -> z) xs
  )

unzip5
  :: Vec n (a,b,c,d,e)
  -> (Vec n a, Vec n b, Vec n c, Vec n d, Vec n e)
unzip5 xs = ( map (\(v,_,_,_,_) -> v) xs
            , map (\(_,w,_,_,_) -> w) xs
            , map (\(_,_,x,_,_) -> x) xs
            , map (\(_,_,_,y,_) -> y) xs
            , map (\(_,_,_,_,z) -> z) xs )
