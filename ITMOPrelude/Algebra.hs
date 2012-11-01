{-# LANGUAGE NoImplicitPrelude, FlexibleInstances #-}
module ITMOPredule.Algebra where

-- Реализовать для всего,
-- что только можно из
import ITMOPrelude.Primitive
-- всевозможные инстансы для классов ниже 

-- Если не страшно, то реализуйте их и для
import ITMOPrelude.List
import ITMOPrelude.Tree

-- Классы
class Monoid a where
    mempty :: a
    mappend :: a -> a -> a

class Monoid a => Group a where
    ginv :: a -> a

newtype Sum a = Sum { getSum :: a }

instance Monoid (Sum Nat) where
    mempty = Sum natZero 
    a `mappend` b = Sum $ getSum a +. getSum b 

instance Monoid (Sum Int) where
    mempty = Sum intZero
    a `mappend` b = Sum $ getSum a .+. getSum b

instance Monoid (Sum Rat) where
    mempty = Sum $ Rat intZero natOne 
    a `mappend` b = Sum $ getSum a %+ getSum b

newtype Product a = Product { getProduct :: a }

instance Monoid (Product Nat) where
    mempty = Product natOne
    a `mappend` b = Product $ getProduct a *. getProduct b

instance Monoid (Product Int) where
    mempty = Product intOne
    a `mappend` b = Product $ getProduct a .*. getProduct b

instance Monoid (Product Rat) where
    mempty = Product $ Rat intOne natOne 
    a `mappend` b = Product $ getProduct a %* getProduct b

instance Monoid (List a) where 
    mempty = Nil
    mappend = (++)

instance Monoid Unit where
    mempty = Unit
    mappend = \_ _ -> Unit

instance Monoid (Maybe a) where 
    mempty = Nothing
    (Just a) `mappend` _ = Just a
    Nothing `mappend` a = a

newtype All = All { getAll :: Bool }
newtype Any = Any { getAny :: Bool }

instance Monoid All where
    mempty = All True
    (All True) `mappend` (All True) = All True
    _ `mappend` _ = All False

instance Monoid Any where
    mempty = Any False
    (Any False) `mappend` (Any False) = Any False
    _ `mappend` _ = Any True

instance Monoid Tri where
    mempty = EQ
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
-- Инстансы писать сюда
