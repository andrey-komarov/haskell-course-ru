{-# LANGUAGE ExistentialQuantification #-}

module Fusion.Internal 
    ( M(..)
    , M8(..)
    , PairS(..)
    , Switch(..)
    , Step(..)
    , Stream(..)
    , empty
    )
where

import Fusion.Size
import Data.Word (Word8)

data M a = N
         | J !a

type M8 = M Word8

infixl 2 :*:
data PairS a b = !a :*: !b
    deriving (Eq, Ord, Show, Read)

data Switch = S1 | S2

data Step s a = Done
              | Skip !s
              | Yield !a !s

data Stream a = forall s . Stream (s -> Step s a) !s  !Size

instance (Show a) => Show (Step s a) where
    show Done = "Done"
    show (Skip _) = "Skip"
    show (Yield a _) = "Yield " ++ show a

instance (Eq a) => Eq (Stream a) where
    (==) = eq

eq :: Eq a => Stream a -> Stream a -> Bool
eq (Stream next1 s1 _) (Stream next2 s2 _) = loop (next1 s1) (next2 s2) where
    loop Done Done = True
    loop (Skip s1') (Skip s2') = loop (next1 s1') (next2 s2')
    loop (Skip s1') x2 = loop (next1 s1') x2
    loop x1 (Skip s2') = loop x1 (next2 s2')
    loop Done _ = False
    loop _ Done = False
    loop (Yield a1 s1') (Yield a2 s2') = a1 == a2 && loop (next1 s1') (next2 s2')
{-# INLINE [0] eq #-}

cmp :: Ord a => Stream a -> Stream a -> Ordering
cmp (Stream next1 s1 _) (Stream next2 s2 _) = loop (next1 s1) (next2 s2) where
    loop Done Done = EQ
    loop (Skip s1') (Skip s2') = loop (next1 s1') (next2 s2')
    loop (Skip s1') x2 = loop (next1 s1') x2
    loop x1 (Skip s2') = loop x1 (next2 s2')
    loop Done _ = LT
    loop _ Done = GT
    loop (Yield x1 s1') (Yield x2 s2') = 
        case compare x1 x2 of
            EQ -> loop (next1 s1') (next2 s2')
            other -> other
{-# INLINE [0] cmp #-}

empty :: Stream a
empty = Stream (\_ -> Done) () 0
{-# INLINE [0] empty #-}
