{-# LANGUAGE FlexibleInstances #-}
module TypedLambda.Types where

import UnTyLambda.Interpreter

import Prelude hiding (any)
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe
import Debug.Trace

infixr 1 :->:

unique = S.toList . S.fromList

{-type Variable = String
data Term
    = Var Variable
    | Lam Variable Term
    | App Term Term deriving (Ord)
-}
type TyVariable = String
data Type
    = TyVar TyVariable
    | Type :->: Type deriving (Eq, Ord)

instance Show Type where
    show (TyVar v) = v
    show (TyVar v :->: t) = v ++ " -> " ++ show t
    show (t1 :->: t2) = "(" ++ show t1 ++ ") -> " ++ show t2

type Equation = (Term, Type)

unusedVar = TyVar `fmap` unused

eqsSys :: Term -> [Equation]
eqsSys e = fst $ runState (eqsSys' e) []

eqsSys' :: Term -> State [TyVariable] [Equation]
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

patchSys :: State [Equation] (Maybe (Type, Type))
patchSys = do
    eqs <- get
{-    let fulleqs = do
                    (e1, t1) <- eqs
                    (e2, t2) <- eqs
                    True <- return $ e1 == e2 && t1 /= t2
                    return (t1, t2)
-}
    let fulleqs = []
    let appeqs = do
                    (App a b, t1) <- eqs
                    (c, t2 :->: t3) <- eqs
                    True <- return $ a == c && t1 /= t3
                    return (t1, t3)
    let lameqs = do
                    (Lam x e, t1 :->: t2) <- eqs
                    (Var x', t3) <- eqs
                    True <- return $ x == x' && t1 /= t3
                    return (t1, t3)
    return $ case fulleqs ++ appeqs ++ lameqs of
        [] -> Nothing
        (x:_) -> Just x

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
                            
infer :: Term -> Maybe Type
infer e = let 
            newE = unifyBound e 
            (res, types) = runState solveSys $ eqsSys $ unifyBound e
          in if res  
                then lookup newE types
                else Nothing

-- \f.\x.\y.f y x
lflip = Lam "f" $ Lam "x" $ Lam "y" $ App (App (Var "f") (Var "y")) (Var "x")
lid = Lam "x" $ Var "x"
lomega = Lam "x" $ App (Var "x") (Var "x")
tflp = (TyVar "a" :->: TyVar "b" :->: TyVar "c") :->: TyVar "b" :->: TyVar "a" :->: TyVar "c"

