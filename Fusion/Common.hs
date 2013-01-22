
module Fusion.Common 

where

import Fusion.Size
import Fusion.Internal

singleton :: a -> Stream a
singleton a = Stream next False 1 where
    next False = Yield a True
    next True = Done
{-# INLINE singleton #-}

streamList :: [a] -> Stream a
streamList s = Stream next s unknownSize where
    next [] = Done
    next (x:xs) = Yield x xs
{-# INLINE [0] streamList #-}

unstreamList :: Stream a -> [a]
unstreamList (Stream next s0 _) = unfold s0 where
    unfold s = case next s of
                    Done -> []
                    Skip s' -> unfold s'
                    Yield a s' -> a : unfold s'
{-# INLINE [0] unstreamList #-}

{-# RULES 
"STREAM stream/unstream fusion" forall s . streamList (unstreamList s) = s 
  #-}

data C s = C0 !s
         | C1 !s

cons :: a -> Stream a -> Stream a
cons a (Stream next0 s0 len) = Stream next (C1 s0) (len + 1) where
    next (C1 s) = Yield a (C0 s)
    next (C0 s) = case next0 s of
                    Done -> Done
                    Skip s' -> Skip (C0 s')
                    Yield a s' -> Yield a (C0 s')
{-# INLINE [0] cons #-}

data E l r = L !l
           | R !r

append :: Stream a -> Stream a -> Stream a
append (Stream next0 s0 len0) (Stream next1 s1 len1) = 
   Stream next (L s0) (len0+len1) 
    where
        next (L s0') = case next0 s0' of
                            Done -> Skip (R s1)
                            Skip s0' -> Skip (L s0')
                            Yield a s0' -> Yield a (L s0')
        next (R s1') = case next1 s1' of
                            Done -> Done
                            Skip s1' -> Skip (R s1')
                            Yield b s1' -> Yield b (R s1')
{-# INLINE [0] append #-}

take :: Int -> Stream a -> Stream a
take n (Stream next s0 _) = Stream next' (s0, n) (maxSize n) where
    next' (s, 0) = Done
    next' (s, n) = case next s of
                        Done -> Done
                        Skip s' -> Skip (s', n)
                        Yield x s' -> Yield x (s', n - 1)
{-# INLINE [0] take #-}

last :: Stream a -> a
last (Stream next s _) = last' s where
    last' s = case next s of
                Done -> error "there is no last of empty stream"
                Skip s' -> last' s'
                Yield x s' -> last'' x s'
    last'' x s = case next s of
                Done -> x
                Skip s' -> last'' x s'
                Yield x' s' -> last'' x' s'
{-# INLINE [0] last #-}

