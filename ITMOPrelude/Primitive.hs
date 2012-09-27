{-# LANGUAGE NoImplicitPrelude #-}
module ITMOPrelude.Primitive where

import Prelude (Show,Read)

---------------------------------------------
-- Синтаксис лямбда-выражений

-- Эквивалентные определения
example1 x  = x
example1'   = \x -> x
example1''  = let y = \x -> x in y
example1''' = y where
    y = \x -> x

-- Снова эквивалентные определения
example2 x y  = x %+ y
example2' x   = \y -> x %+ y
example2''    = \x -> \y -> x %+ y
example2'''   = \x y -> x %+ y
example2''''  = let z = \x y -> x %+ y in z
example2''''' = z where
    z x = \y -> x %+ y

-- Зацикленное выражение
undefined = undefined

-- Ниже следует реализовать все термы, состоящие из undefined заглушки.
-- Любые термы можно переписывать (natEq и natLt --- хорошие кандидаты).

-------------------------------------------
-- Примитивные типы

-- Тип с единственным элементом
data Unit = Unit deriving (Show,Read)

-- Пара, произведение
data Pair a b = Pair { fst :: a, snd :: b } deriving (Show,Read)

-- Вариант, копроизведение
data Either a b = Left a | Right b deriving (Show,Read)

-- Частый частный случай, изоморфно Either Unit a
data Maybe a = Nothing | Just a deriving (Show,Read)

-- Частый частный случай, изоморфно Either Unit Unit
data Bool = False | True deriving (Show,Read)

-- Следует отметить, что встроенный if с этим Bool использовать нельзя,
-- зато case всегда работает.

-- Ну или можно реализовать свой if
if' True a b = a
if' False a b = b

-- Трихотомия. Замечательный тип, показывающий результат сравнения
data Tri = LT | EQ | GT deriving (Show,Read)

cmpNeg :: Tri -> Tri
cmpNeg LT = GT
cmpNeg EQ = EQ
cmpNeg GT = LT

-------------------------------------------
-- Булевы значения

-- Логическое "НЕ"
not :: Bool -> Bool
not True = False
not False = True

infixr 3 &&
-- Логическое "И"
(&&) :: Bool -> Bool -> Bool
True  && x = x
False && _ = False

infixr 2 ||
-- Логическое "ИЛИ"
(||) :: Bool -> Bool -> Bool
True  || _ = True
False || x = x

-------------------------------------------
-- Натуральные числа

data Nat = Zero | Succ Nat deriving (Show,Read)

natZero = Zero     -- 0
natOne = Succ Zero -- 1

-- Сравнивает два натуральных числа
natCmp :: Nat -> Nat -> Tri
natCmp Zero Zero = EQ
natCmp Zero _ = LT 
natCmp _ Zero = GT
natCmp (Succ n) (Succ m) = natCmp n m

-- n совпадает с m 
natEq :: Nat -> Nat -> Bool
natEq n m = case natCmp n m of
    EQ -> True
    _ -> False 

-- n меньше m
natLt :: Nat -> Nat -> Bool
natLt n m = case natCmp n m of
    LT -> True
    _ -> False

infixl 6 +.
-- Сложение для натуральных чисел
(+.) :: Nat -> Nat -> Nat
Zero     +. m = m
(Succ n) +. m = Succ (n +. m)

infixl 6 -.
-- Вычитание для натуральных чисел
(-.) :: Nat -> Nat -> Nat
n -. Zero = n
(Succ n) -. (Succ m) = n -. m 

infixl 7 *.
-- Умножение для натуральных чисел
(*.) :: Nat -> Nat -> Nat
Zero     *. m = Zero
(Succ n) *. m = m +. (n *. m)

-- Целое и остаток от деления n на m
natDivMod :: Nat -> Nat -> Pair Nat Nat
natDivMod n m = case n `natLt` m of
    True -> Pair Zero n
    False -> Pair (Succ div) mod where
        Pair div mod = (n -. m) `natDivMod` m 

natDiv n = fst . natDivMod n -- Целое
natMod n = snd . natDivMod n -- Остаток

-- Поиск GCD алгоритмом Евклида (должен занимать 2 (вычислителельная часть) + 1 (тип) строчки)
gcd :: Nat -> Nat -> Nat
gcd n Zero = n
gcd n m = gcd m $ n `natMod` m

-------------------------------------------
-- Целые числа

-- Требуется, чтобы представление каждого числа было единственным
data Int = Pos Nat | Neg Nat deriving (Show,Read)

intZero   = Pos natZero-- 0
intOne    = Pos natOne-- 1
intNegOne = Neg natZero -- -1

-- n -> - n
intNeg :: Int -> Int
intNeg (Pos Zero) = Pos Zero
intNeg (Pos (Succ n)) = Neg n
intNeg (Neg n) = Pos $ Succ n

-- Дальше также как для натуральных
intCmp :: Int -> Int -> Tri
intCmp (Neg _) (Pos _) = LT
intCmp (Pos n) (Pos m) = n `natCmp` m
intCmp (Neg n) (Neg m) = m `natCmp` n
intCmp _ _ = GT

intEq :: Int -> Int -> Bool
intEq n m = case n `intCmp` m of
    EQ -> True
    _ -> False

intLt :: Int -> Int -> Bool
intLt n m = case n `intCmp` m of
    LT -> True
    _ -> False

infixl 6 .+., .-.
-- У меня это единственный страшный терм во всём файле
(.+.) :: Int -> Int -> Int
(Pos n) .+. (Pos m) = Pos $ n +. m
(Neg n) .+. (Neg m) = Neg $ Succ $ n +. m
(Pos (Succ n)) .+. (Neg (Succ m)) = Pos n .+. Neg m
(Pos Zero) .+. (Neg m) = Neg m
(Pos (Succ n)) .+. (Neg Zero) = Pos n
n .+. m = m .+. n 

(.-.) :: Int -> Int -> Int
n .-. m = n .+. (intNeg m)

infixl 7 .*.
(.*.) :: Int -> Int -> Int
(Pos n) .*. (Pos m) = Pos (n *. m)
n .*. m@(Neg _) = intNeg $ n .*. intNeg m 
n .*. m = m .*. n

-------------------------------------------
-- Рациональные числа

data Rat = Rat Int Nat

ratNeg :: Rat -> Rat
ratNeg (Rat x y) = Rat (intNeg x) y

ratNormalize :: Rat -> Rat
ratNormalize (Rat (Pos n) m) = Rat (Pos $ n `natDiv` g) (m `natDiv` g) where
    g = gcd n m 

-- У рациональных ещё есть обратные элементы
ratInv :: Rat -> Rat
ratInv (Rat (Pos n) m) = Rat (Pos m) n
ratInv (Rat n@(Neg _) m) = ratNeg $ Rat (intNeg n) m

-- Дальше как обычно
ratCmp :: Rat -> Rat -> Tri
ratCmp (Rat p1 q1) (Rat p2 q2) = (p1 .*. Pos q2) `intCmp` (p2 .*. Pos q1)

ratEq :: Rat -> Rat -> Bool
ratEq n m = case n `ratCmp` m of
    EQ -> True
    _ -> False 

ratLt :: Rat -> Rat -> Bool
ratLt n m = case n `ratCmp` m of
    LT -> True
    _ -> False

infixl 7 %+, %-
(%+) :: Rat -> Rat -> Rat
(Rat p1 q1) %+ (Rat p2 q2) = ratNormalize $ Rat p q
    where p = p1 .*. Pos q2 .+. p2 .*. Pos q2 
          q = q1 *. q2

(%-) :: Rat -> Rat -> Rat
n %- m = n %+ (ratNeg m)

infixl 7 %*, %/
(%*) :: Rat -> Rat -> Rat
(Rat p1 q1) %* (Rat p2 q2) = ratNormalize $ Rat (p1 .*. p2) (q1 *. q2)

(%/) :: Rat -> Rat -> Rat
n %/ m = n %* (ratInv m)

-------------------------------------------
-- Операции над функциями.
-- Определены здесь, но использовать можно и выше

infixr 9 .
f . g = \ x -> f (g x)

infixr 0 $
f $ x = f x

-- Эквивалентные определения
example3   a b c = gcd a (gcd b c)
example3'  a b c = gcd a $ gcd b c
example3'' a b c = ($) (gcd a) (gcd b c)

-- И ещё эквивалентные определения
example4  a b x = (gcd a (gcd b x))
example4' a b = gcd a . gcd b
