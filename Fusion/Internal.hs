{-# LANGUAGE ExistentialQuantification #-}

module Fusion.Internal 
    ( M(..)
    , PairS(..)
    , Switch(..)
    , Step(..)
    , Stream(..)
    , empty
    )
where

data M a = N
         | J !a

infixl 2 :*:
data PairS a b = !a :*: !b
--    deriving (Eq, Ord, Show, Read)

data Switch = S1 | S2

data Step s a = Done
              | Skip !s
              | Yield !a !s

data Stream a = forall s . Stream (s -> Step s a) !s

{-
instance (Show a) => Show (Step s a) where
    show Done = "Done"
    show (Skip _) = "Skip"
    show (Yield a _) = "Yield " ++ show a
-}

empty :: Stream a
empty = Stream (\_ -> Done) ()
{-# INLINE [0] empty #-}
