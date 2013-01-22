import Fusion.Newton
import Fusion.Common as F
import Fusion.Internal
import Data.List

f x = x * x - 5
f2 x = x
f3 x = exp x
f4 x = sin x
f5 x = exp x - 2

funs = [f, f2, f3, f4, f5]

main = do
    sequence $ map (\f -> 
        let root = findRoot 1000 0.00001 10 20 f
        in putStrLn $ "f " ++ show root ++ " = " ++ show (f root)
     ) funs
