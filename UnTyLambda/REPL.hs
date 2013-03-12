-- REPL for untyped lambda calculus
module UnTyLambda.REPL where

import Monstupar
import UnTyLambda.Interpreter
import TypedLambda.Types
import System.IO

-- Парсим строку в терм
parseLambda :: Monstupar Char Term
parseLambda = do
    spaces
    t <- parseT
    spaces >> eof
    return t

--------------------------------------------------------------------------------
-- Заметье, что грамматика лямбда-выражений леворекурсивна.
-- Перед тем как бросаться кодить, сначала уберите леворекурсивность на бумаге,
-- а потом напишите получившуюся грамматику в EBNF вот сюда:
-- \x.\y.\z.x y z \x.(\y.\z.((x y) z))
--
-- ST ::= ( T ) | V
-- T ::= L | ST+
-- L ::= \ V . T
-- V ::= alphanum+
--
-- прямо сюда, да
--------------------------------------------------------------------------------

infixl 2 &.&
(&.&) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(f &.& g) x = f x && g x

infixl 3 |.|
(|.|) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(f |.| g) x = f x || g x

isDigit :: Char -> Bool
isDigit = ('0' <=) &.& (<= '9')

isLetter :: Char -> Bool
isLetter = (('a' <=) &.& (<= 'z')) |.| (('A' <=) &.& (<= 'Z'))

parseV :: Monstupar Char String
parseV = many1 $ like (isLetter |.| isDigit)

parseST :: Monstupar Char Term
parseST = brackets <|> var where 
    brackets = do
                char '(' >> spaces
                t <- parseT
                spaces >> char ')' >> spaces
                return t
    var = do
            v <- parseV
            spaces
            return $ Var v

parseT :: Monstupar Char Term
parseT = parseL <|> parseA where
    parseA = do
                ax <- many1 $ spaces >> parseST
                return $ foldl1 App ax

parseL :: Monstupar Char Term
parseL = do
    v <- char '\\' >> spaces >> parseV
    spaces
    t <- char '.' >> spaces >> parseT
    spaces
    return $ Lam v t
     

-- Красиво печатаем терм (можно с лишними скобками, можно без)
prettyPrint :: Term -> String
prettyPrint = show

-- Собственно сам REPL. Первый аргумент — максимальное число итераций при
-- попытке нормализации стратегией из второго аргумента.
replLoop :: Integer -> (Integer -> Term -> Term) -> IO ()
replLoop patience strategy = do
    putStr "> " 
    hFlush stdout
    s <- getLine
    let t = runParser parseLambda s
    putStrLn $ case t of
                Left _ -> "incorrect"
                Right (_, t) -> let 
--                    t' = strategy patience t 
                    t' = t
                    tp = infer t'
                    pp = prettyPrint t'
                    in case tp of
                        Nothing -> pp
                        Just tp -> pp ++ " :: " ++ show tp
    replLoop patience strategy

    

-- Диалог с (replLoop 100 no) должен выглядеть так:
-- > \x . (\y . y) x x
-- \x . x x
