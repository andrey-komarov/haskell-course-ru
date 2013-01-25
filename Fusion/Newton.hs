{-# LANGUAGE BangPatterns #-}

module Fusion.Newton
    ( findRoot
    )
where

import Fusion.Common as F
import Fusion.Internal

--data T = T {-# UNPACK #-} !Double
--           {-# UNPACK #-} !Double

derivative :: Double -> (Double -> Double) -> Double -> Double
derivative dx f x = (f (x + dx) - f (x - dx)) / (2 * dx)
{-# INLINE [0] derivative #-}

newtonStep :: (Double -> Double) -> (Double -> Double) -> Double -> Double
newtonStep f df x = x - f x / df x
{-# INLINE [0] newtonStep #-}

findRoot :: Double -> (Double -> Double) -> Double -> Double
findRoot eps f x0 = 
    F.last $! F.takeWhile' ( (> eps) . abs . f )
                       $! F.iterate (newtonStep f (derivative 0.001 f)) x0
{-# INLINE [0] findRoot #-}

{- approx :: Double -> Double -> Double -> (Double -> Double) -> Stream Double
approx !eps !x1 !x2 !f = Stream next (T x1 x2) where
    next (T x x1) = let dx = (f x - f x1) / (x - x1)
                        {-# INLINE dx #-}
                        x' = x - f x / dx
                    in if abs (f x) < eps
                           then Done
                           else Yield x' (T x' x)
    {-# INLINE next #-}
{-# INLINE [0] approx #-}
-}

{-
findRoot :: Double -> Double -> Double -> (Double -> Double) -> Double
findRoot eps x0 x1 f = F.last $ approx eps x0 x1 f
{-# INLINE [0] findRoot #-}
-}
