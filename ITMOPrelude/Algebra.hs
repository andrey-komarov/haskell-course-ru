{-# LANGUAGE NoImplicitPrelude, FlexibleInstances #-}
module ITMOPrelude.Algebra where

import ITMOPrelude.Primitive
import ITMOPrelude.List

class Monoid a where
    mzero :: a
    mappend :: a -> a -> a

class Monoid a => Group a where
    ginv :: a -> a

newtype Sum a = Sum { getSum :: a }

instance Monoid (Sum Nat) where
    mzero = Sum natZero 
    a `mappend` b = Sum $ getSum a +. getSum b 

instance Monoid (Sum Int) where
    mzero = Sum intZero
    a `mappend` b = Sum $ getSum a .+. getSum b

instance Monoid (Sum Rat) where
    mzero = Sum $ Rat intZero natOne 
    a `mappend` b = Sum $ getSum a %+ getSum b

newtype Product a = Product { getProduct :: a }

instance Monoid (Product Nat) where
    mzero = Product natOne
    a `mappend` b = Product $ getProduct a *. getProduct b

instance Monoid (Product Int) where
    mzero = Product intOne
    a `mappend` b = Product $ getProduct a .*. getProduct b

instance Monoid (Product Rat) where
    mzero = Product $ Rat intOne natOne 
    a `mappend` b = Product $ getProduct a %* getProduct b

instance Monoid (List a) where 
    mzero = Nil
    mappend = (++)

instance Monoid Unit where
    mzero = Unit
    mappend = \_ _ -> Unit

instance Monoid (Maybe a) where 
    mzero = Nothing
    (Just a) `mappend` _ = Just a
    Nothing `mappend` a = a

newtype All = All { getAll :: Bool }
newtype Any = Any { getAny :: Bool }

instance Monoid All where
    mzero = All True
    (All True) `mappend` (All True) = All True
    _ `mappend` _ = All False

instance Monoid Any where
    mzero = Any False
    (Any False) `mappend` (Any False) = Any False
    _ `mappend` _ = Any True

instance Monoid Tri where
    mzero = EQ
    EQ `mappend` a = a
    a `mappend` _ = a

instance Group (Sum Int) where
    ginv = Sum . intNeg . getSum

instance Group (Sum Rat) where
    ginv = Sum . ratNeg . getSum

instance Group (Product Rat) where
    ginv = Product . ratInv . getProduct 

instance Group Unit where
    ginv = \_ -> Unit

