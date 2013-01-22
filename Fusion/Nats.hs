import Fusion.Internal
import Fusion.Size
import Fusion.Common as SC

isqrt :: Int -> Int
isqrt n = round $ sqrt $ fromIntegral n

isPrime :: Int -> Bool
isPrime n = all ((/= 0) . (n `mod`)) [2..isqrt n]

nats :: Stream Int
nats = Stream (\n -> Yield n (n+1)) 0 unknownSize

primes :: Stream Int
primes = Stream next 2 unknownSize where
    next n
     | isPrime n = Yield n (n+1)
     | otherwise = Skip (n+1)

main = do
    print $ SC.last $ SC.take 10 nats
