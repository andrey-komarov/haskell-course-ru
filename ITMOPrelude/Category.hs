{-# LANGUAGE NoImplicitPrelude #-}
module ITMOPrelude.Category where

import ITMOPrelude.Primitive
import ITMOPrelude.List
import ITMOPrelude.Algebra
import ITMOPrelude.Tree

class Category cat where
    id :: cat a a
    (<.>) :: cat b c -> cat a b -> cat a c

instance Category (->) where 
    id = \x -> x 
    (<.>) = (.)

class Functor f where
    fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
    f `fmap` Nothing = Nothing
    f `fmap` Just a = Just $ f a

instance Functor List where
    f `fmap` Nil = Nil
    f `fmap` Cons a b = Cons (f a) $ f `fmap` b

instance Functor (Either e) where
    f `fmap` Left e = Left e
    f `fmap` Right a = Right $ f a

instance Functor Tree where
    f `fmap` Leaf = Leaf
    f `fmap` Node a left right = Node (f a) (f `fmap` left) (f `fmap` right)

class Functor m => Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b

instance Monad Maybe where
    return = Just
    Nothing >>= f = Nothing
    Just a >>= f = f a

instance Monad (Either e) where
    return = Right
    Left e >>= f = Left e
    Right a >>= f = f a

instance Monad List where
    return a = Cons a Nil
    Nil >>= f = Nil
    Cons a b >>= f = f a ++ (b >>= f)

