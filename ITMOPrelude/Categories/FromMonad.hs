{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, UndecidableInstances #-}
module ITMOPrelude.Categories.FromMonad where
import ITMOPrelude.Categories hiding ((.))

-- Эти
import ITMOPrelude.Categories.MonadJoin
import ITMOPrelude.Categories.MonadFish

import ITMOPrelude.Primitive

-- делаем нас

instance Monad m => Functor m where
    fmap f a = a >>= (return . f)

instance Monad m => MonadJoin m where
    returnJoin = return
    join = (>>= id)

instance Monad m => MonadFish m where
    returnFish = return
    (f >=> g) a =f a >>= g 
