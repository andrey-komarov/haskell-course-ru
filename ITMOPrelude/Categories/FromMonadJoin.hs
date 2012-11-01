{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, UndecidableInstances #-}
module ITMOPrelude.Categories.FromMonadJoin where
import ITMOPrelude.Categories.MonadJoin

-- Эти
import ITMOPrelude.Primitive
import ITMOPrelude.Categories
import ITMOPrelude.Categories.MonadFish

instance MonadJoin m => Monad m where
    return = returnJoin
    m >>= f = join $ f `fmap` m 

instance MonadJoin m => MonadFish m where
    returnFish = returnJoin
    (f >=> g) a = join $ g `fmap` f a

-- делаем из нас
