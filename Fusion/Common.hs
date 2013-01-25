{-# LANGUAGE BangPatterns #-}
module Fusion.Common 

where

import Fusion.Internal

last :: Stream a -> a
last (Stream next s) = last' s where
    last' !s = case next s of
                Done -> error "there is no last of empty stream"
                Skip s' -> last' s'
                Yield x s' -> last'' x s'
    {-# INLINE last' #-}
    last'' !x !s = case next s of
                Done -> x
                Skip s' -> last'' x s'
                Yield x' s' -> last'' x' s'
    {-# INLINE last'' #-}
{-# INLINE [0] last #-}

takeWhile' :: (a -> Bool) -> Stream a -> Stream a
takeWhile' p (Stream next s) = Stream next' (S1, s) where
    next' !(c, s) = case next s of
                Done -> Done
                Skip s' -> Skip (c, s')
                Yield x s' | p x -> Yield x (c, s')
                           | otherwise -> case c of
                                            S1 -> Yield x (S2, s')
                                            S2 -> Done
    {-# INLINE next' #-}
{-# INLINE [0] takeWhile' #-}

{-
takeWhile :: (a -> Bool) -> Stream a -> Stream a
takeWhile p (Stream next s) = Stream next' s where
    next' !s = case next s of
                Done -> Done
                Skip s' -> Skip s'
                Yield x s' | p x -> Yield x s'
                           | otherwise -> Done
    {-# INLINE next' #-}
{-# INLINE [0] takeWhile #-}
-}

iterate :: (a -> a) -> a -> Stream a
iterate f x = Stream next x where
    next !x = Yield x (f x)
    {-# INLINE next #-}
{-# INLINE [0] iterate #-}
