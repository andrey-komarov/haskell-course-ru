module Fusion.Newton
    ( findRoot
    , approx
    )
where

import Fusion.Common as F
import Fusion.Internal
import Fusion.Size

approx :: Int -> Double -> Double -> Double -> (Double -> Double) -> Stream Double
approx n eps x1 x2 f = Stream next (n, x2) unknownSize where
    next (0, x) = Done
    next (n, x) = let dx = (f x - f x1) / (x - x1)
                      x' = x - f x / dx
                  in if abs (f x) < eps
                      then Done
                      else Yield x' (n-1, x')

approx2 :: Int -> Double -> Double -> Double -> (Double -> Double) -> Stream Double
approx2 n eps x1 x2 f = Stream next (n, x1, x2) unknownSize where
    next (0, _, _) = Done
    next (n, x, x1) = let dx = (f x - f x1) / (x - x1)
                          x' = x - f x / dx
                      in if abs (f x) < eps
                           then Done
                           else Yield x' (n-1, x', x)

findRoot :: Int -> Double -> Double -> Double -> (Double -> Double) -> Double
findRoot n eps x0 x1 f = F.last $ approx2 n eps x0 x1 f
