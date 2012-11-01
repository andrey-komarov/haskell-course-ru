{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, UndecidableInstances #-}
module ITMOPrelude.Categories.FromMonadFish where
import ITMOPrelude.Categories.MonadFish

-- Эти
import ITMOPrelude.Categories hiding ((.))
import ITMOPrelude.Categories.MonadJoin

import ITMOPrelude.Primitive (undefined, (.))

-- делаем из нас
instance MonadFish m => Monad m where
    return = returnFish
    f >>= g = (id >=> g) f

instance MonadFish m => Functor m where
    fmap f a = a >>= (return . f)

instance MonadFish m => MonadJoin m where
    returnJoin = returnFish 
    join = id >=> id 
