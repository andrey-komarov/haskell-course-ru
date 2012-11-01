{-# LANGUAGE NoImplicitPrelude #-}
module ITMOPrelude.IO where

import ITMOPrelude.Primitive
import ITMOPrelude.List
import ITMOPrelude.Categories

data RealWorld = RealWorld
    { stdIn :: List Nat
    , stdOut :: List Nat
    , exitCode :: Nat }

type IO a = State RealWorld a

getNat :: IO Nat
getNat = State $ \s -> case s of
    RealWorld stdIn stdOut exitCode -> case stdIn of
        Cons x xs -> (RealWorld xs stdOut exitCode, x)
        Nil -> undefined

putNat :: Nat -> IO ()
putNat n = State $ \s -> case s of
    RealWorld stdIn stdOut exitCode -> 
                (RealWorld stdIn (Cons n stdOut) exitCode, ())

setExitCode :: Nat -> IO ()
setExitCode code = State $ \s -> case s of 
    RealWorld stdIn stdOut _ -> (RealWorld stdIn stdOut code, ())
