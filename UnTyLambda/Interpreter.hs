{-# LANGUAGE ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- В данном задании требуется реализовать интерпретатор для
-- нетипизированной лямбды
--------------------------------------------------------------------------------

module UnTyLambda.Interpreter where

-- Какие-то импорты. Заметьте, что в этом задании надо
-- использовать обычную Prelude
import Prelude hiding (catch)
import Control.Exception

------------------------------------------------------------
-- Определение дататайпа для нетипизированной лямбды
type Variable = String
data Term = Var Variable | Lam Variable Term | App Term Term deriving (Show,Read)

------------------------------------------------------------
-- Дальше всё на ваше усмотрение

-- Если внутри будете использовать именованное представление, то
-- я тут решил немного вам помочь
-- (иначе говоря, код из этого раздела можно совсем выкинуть,
-- если хочется)

free (Var v)    = [ v ]
free (Lam v t)  = filter (/= v) . free $ t
free (App t t') = (free t) ++ (free t')

subst :: Term -> Variable -> Term -> Term
subst t@(Var v)   var what = if v == var then what else t
subst t@(Lam v b) var what = if v == var then t else Lam v (subst b var what)
subst (App t t')  var what = App (subst t var what) (subst t' var what)

newname :: [Variable] -> Variable -> Variable 
newname fv = head . filter (not . flip elem fv) . iterate ('_':)

deny:: [String] -> Term -> Term
deny d (Var v) = Var $ newname d v
deny d (Lam v t) = Lam v' $ subst t v (Var v') where v' = newname (d ++ free t) v
deny d (App t1 t2) = App (deny d t1) (deny d t2)
--- ...

------------------------------------------------------------
-- За исключением того, что требуется реализовать следующие
-- стратегии нормализации (они все принимают максимальное
-- число шагов интерпретатора в качестве первого 
-- параметра (n); если за n шагов нормализовать не удаётся,
-- то следует бросать error, тестер его поймает):

wh, no, wa, sa :: Integer -> Term -> Term

-- Редукция аппликативным порядком
sa 0 t = error $ "Too long sequence at [" ++ show t ++ "]"
sa n t 
    | reduced = sa (n - 1) rest
    | otherwise = t
    where (reduced, rest) = saOne t 

saOne :: Term -> (Bool, Term)
saOne t@(Var v) = (False, t)
saOne (Lam v t) = (reduced, Lam v rest)
    where (reduced, rest) = saOne t
saOne t@(App t1 t2) = if reducedRight
        then (True, App t1 t2')
        else case t1 of 
            (Lam v t1'') -> (True, subst (deny (free t2) t1'') v t2) where
                (_, t1''') = saOne t1'' 
            _ -> (reducedLeft, App t1' t2)
    where 
        (reducedRight, t2') = saOne t2
        (reducedLeft, t1') = saOne t1

-- Нормализация нормальным порядком
no 0 t = error $ "Too long sequence at [" ++ show t ++ "]"
no n t 
    | reduced = no (n - 1) rest
    | otherwise = t
    where (reduced, rest) = noOne t

noOne :: Term -> (Bool, Term)
noOne (App (Lam v t1) t2) = (True, subst (deny (free t2) t1) v t2)
noOne t@(Var v) = (False, t)
noOne (Lam v t) = (reduced, Lam v rest) 
    where (reduced, rest) = noOne t 
noOne t@(App t1 t2) = if reducedLeft 
                        then (True, App t1' t2) 
                        else if reducedRight
                            then (True, App t1 t2')
                            else (False, t)
    where
        (reducedLeft, t1') = noOne t1
        (reducedRight, t2') = noOne t2
        fv = free t2

-- Редукция в слабую головную нормальную форму
wh = undefined

-- (*) (не обязательно) Редукция "слабым" аппликативным порядком.
-- Отличается от обычного аппликативного тем, что не лезет внутрь
-- лямбд и правые части аппликаций, когда это возможно.
wa = undefined

-- Замечание: cкорость работы вашего интерпретатора специально не оценивается,
-- потому можно использовать свой изоморфный (с точностью до альфа-конверсии)
-- тип для представления термов и преобразовывать Term в него и обратно.

-- Перечисление всех этих порядков (в порядке отличном от
-- определения, да)
orders =
    [ ("wh", wh)
    , ("no", no)
--    , ("wa", wa) -- Можно раскоментировать, да
    , ("sa", sa) ]

------------------------------------------------------------
-- Игнорируйте это, если выглядит непонятно
pall term = mapM_ $ \(d, x) -> putStr (d ++ ": ") >> catch (let t = x 1000 term in seq t (print t)) (\(e :: SomeException) -> print e)
testfuncs funcs = mapM_ $ \t -> putStr "===== " >> print t >> pall t funcs

------------------------------------------------------------
-- Сюда можно добавлять тесты
lamxx = Lam "x" $ App (Var "x") (Var "x")
omega = App lamxx lamxx
lamid = Lam "x" $ Var "x"
lamconst = Lam "x" $ Lam "y" $ Var "x"
ololo = (lamconst `App` lamid) `App` omega
test1 = Lam "x" $ (Lam "y" $ Var "y") `App` (Var "x")
test2 = (Lam "x" $ Lam "y" $ Var "x") `App` (Var "y")

test = testfuncs orders
    [ Var "a"
    , Lam "x" $ (Lam "y" $ Var "y") `App` (Var "x")
    , (Lam "x" $ Lam "y" $ Var "x") `App` (Var "y")
    , omega
    ]

------------------------------------------------------------
-- Немного теоретических замечаний, если они вас волнуют
--
-- Следует специально отметить, что поскольку в конце теста
-- результат вычисления печатают, то ленивость Haskell не
-- влияет на семантику интерпретируемого исчисления.
--
-- Чтобы это особенно подчеркнуть в тестере выше я написал
-- seq в интересном месте (хотя конкретно это там ничего не
-- гарантирует, на самом-то деле).
