{-# LANGUAGE FlexibleInstances #-}
module TypedLambda.Types where

import Data.Foldable hiding (elem)
import Prelude hiding (any)
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace

infixr 1 :->:

unique = S.toList . S.fromList

type Variable = String
data Expr
    = Var Variable
    | Lam Variable Expr
    | App Expr Expr deriving (Ord)

instance Show Expr where
    show (Var x) = x
    show (Lam x e) = "\\" ++ x ++ "." ++ show e
    show (App e1@(Lam _ _) e2) = "(" ++ show e1 ++ ")" ++ show e2
    show (App e1 (Var v)) = show e1 ++ " " ++ v
    show (App e1 e2) = show e1 ++ "(" ++ show e2 ++ ")"

free (Var v)    = [ v ]
free (Lam v t)  = filter (/= v) . free $ t
free (App t t') = (free t) ++ (free t')

subst :: Expr -> Variable -> Expr -> Expr
subst t@(Var v)   var what = if v == var then what else t
subst t@(Lam v b) var what = if v == var then t else Lam v (subst b var what)
subst (App t t')  var what = App (subst t var what) (subst t' var what)

newname :: [Variable] -> Variable -> Variable 
newname fv = head . filter (not . flip elem fv) . iterate ('_':)

type TyVariable = String
data Type
    = TyVar TyVariable
    | Type :->: Type deriving (Eq, Ord)

instance Show Type where
    show (TyVar v) = v
    show ((TyVar v) :->: t) = v ++ " -> " ++ show t
    show (t1 :->: t2) = "(" ++ show t1 ++ ") -> " ++ show t2

type Equation = (Expr, Type)

unused :: State [TyVariable] TyVariable
unused = do
    used <- get
    let new = head $ filter (not . (`elem` used)) $ map show [1..]
    put $ new:used
    return new 

unusedVar = TyVar `fmap` unused

eqsSys :: Expr -> [Equation]
eqsSys e = fst $ runState (eqsSys' e) []

eqsSys' :: Expr -> State [TyVariable] [Equation]
eqsSys' e@(Var v) = do 
    var <- unusedVar
    return [(e, var)]
eqsSys' e@(App v1 v2) = do
    a <- unusedVar
    b <- unusedVar
    eqs1 <- eqsSys' v1
    eqs2 <- eqsSys' v2
    return $ [(v2, a), (e, b), (v1, a :->: b)] ++ eqs1 ++ eqs2
eqsSys' e@(Lam v e') = do
    a <- unusedVar
    b <- unusedVar
    eqs1 <- eqsSys' e'
    return $ [(Var v, a), (e', b), (e, a :->: b)] ++ eqs1

unifyBound :: Expr -> Expr 
unifyBound e = fst $ runState (unifyBound' e) (M.empty, free e)

unifyBound' :: Expr -> State (M.Map Variable Variable, [TyVariable]) Expr
unifyBound' (Var v) = do
    (m, used) <- get
    return $ Var $ case M.lookup v m of
        Nothing -> v
        Just v' -> v'
unifyBound' e@(App t1 t2) = do
    t1' <- unifyBound' t1
    t2' <- unifyBound' t2
    return $ App t1' t2'
unifyBound' (Lam x t) = do
    (m, used) <- get
    let new = fst $ runState unused used
    put $ (M.insert x new m, new:used)
    e <- unifyBound' t
    (_, used') <- get
    put $ (m, used')
    return $ Lam new e

eq :: Expr -> Expr -> Bool
eq (Var v) (Var v') = v == v'
eq (Lam v1 e1) (Lam v2 e2) = v1 == v2 && e1 `eq` e2
eq (App e1 e2) (App e1' e2') = e1 `eq` e1' && e2 `eq` e2'
eq _ _ = False

instance Eq Expr where
    e1 == e2 = free e1 == free e2 && newE1 `eq` newE2 where
        newE1 = unifyBound e1
        newE2 = unifyBound e2
        fv = free e1

patchSys :: State [Equation] (Maybe (Type, Type))
patchSys = do
    eqs <- get
    let fulleqs = do
                    (e1, t1) <- eqs
                    (e2, t2) <- eqs
                    True <- return $ e1 == e2 && t1 /= t2
                    return $ (t1, t2)
    let appeqs = do
                    (App a b, t1) <- eqs
                    (c, t2 :->: t3) <- eqs
                    True <- return $ a == c && t1 /= t3
                    return $ (t1, t3)
    let lameqs = do
                    (Lam x e, t1 :->: t2) <- eqs
                    (Var x', t3) <- eqs
                    True <- return $ x == x' && t1 /= t3
                    return $ (t1, t3)
    return $ case fulleqs ++ appeqs ++ lameqs of
        [] -> Nothing
        (x:_) -> Just x
{-    return $ do
        ((e1, t1), (e2, t2)) <- 
            find (\((e1, t1), (e2, t2)) -> e1 == e2 && t1 /= t2) $
                    [(eq1, eq2) | eq1 <- eqs, eq2 <- eqs]
            `mappend` 
            find (\(
        return $ (t1, t2) -}

replace :: Type -> Type -> Type -> Type
replace t what to | t == what = to
replace t@(TyVar x) what to = t
replace (t1 :->: t2) what to = replace t1 what to :->: replace t2 what to

replaceMany :: Type -> Type -> [Equation] -> [Equation]
replaceMany t1 t2 = map (\(e, t) -> (e, replace t t1 t2))

mutual :: Type -> Type -> Bool
mutual t1 t2 = t1 `inside` t2 || t2 `inside` t1

inside :: Type -> Type -> Bool
inside t1 t2 | t1 == t2 = True
inside t (TyVar _) = False
inside t (t1 :->: t2) = t `inside` t1 || t `inside` t2

solveSys :: State [Equation] Bool
solveSys = do
    patch <- patchSys 
    eee <- get
    case patch of
        Nothing -> return True 
        Just (t1, t2) -> do
            eqs <- get
            if mutual t1 t2
             then return False
             else do 
                    if t1 < t2 
                        then put $ unique $ replaceMany t1 t2 eqs
                        else put $ unique $ replaceMany t2 t1 eqs
                    solveSys
                            
infer :: Expr -> Maybe Type
infer e = let 
            newE = unifyBound e 
            (res, types) = runState solveSys $ eqsSys $ unifyBound e
          in case res of
                False -> Nothing
                True -> lookup newE types

-- \f.\x.\y.f y x
lflip = Lam "f" $ Lam "x" $ Lam "y" $ App (App (Var "f") (Var "y")) (Var "x")
lid = Lam "x" $ Var "x"
lomega = Lam "x" $ App (Var "x") (Var "x")
tflp = (TyVar "a" :->: TyVar "b" :->: TyVar "c") :->: TyVar "b" :->: TyVar "a" :->: TyVar "c"

