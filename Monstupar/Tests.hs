module Monstupar.Tests where

import Monstupar.Core
import Monstupar.Derived

--------------------------------------------------------------------------------
-- В помощь хозяйке

mustParse :: [s] -> Monstupar s a -> Bool
mustParse s p = case runParser p s of
    Left  _ -> False
    Right _ -> True

mustFail :: [s] -> Monstupar s a -> Bool
mustFail s = not . mustParse s

infixl 2 &.&
(&.&) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(&.&) p1 p2 x = p1 x && p2 x

--------------------------------------------------------------------------------
-- Тесты

-- Правильная скобочная последовательность
balPar :: Monstupar Char ()
balPar = bp >> eof where
    bp = (do
          char '('
          bp
          char ')'
          bp) <|> ok

balParTest = mustParse ""
         &.& mustFail  "("
         &.& mustFail  ")"
         &.& mustParse "()"
         &.& mustParse "(())()(())()"
         &.& mustFail  "())()(())()"
         &.& mustFail  "(())()(()()"
         &.& mustFail  "())()(()()"
         $ balPar

-- Список натуральных чисел
-- тут следует использовать класс Read
digit :: Monstupar Char Char
digit = oneOf ['0'..'9']

int :: Monstupar Char Integer
int = do
    xs <- many1 digit
    return $ read xs 

natList :: Monstupar Char [Integer]
natList = do
            res <- parse
            eof 
            return res where 
    parse = do 
                fst <- int
                rest <- many $ char ',' >> int
                return $ fst:rest

natListTest = mustFail  ""
          &.& mustParse "0"
          &.& mustParse "0,1"
          &.& mustFail  "0,1,"
          &.& mustParse "10,20,12,3423,2342,234,2234,2342,22342,22232,17583,9573"
          &.& mustFail  "10,20,12,3423,2342,234,-2234,2342,22342,22232,17583,9573"
          &.& mustFail  "10,20,12,3423,0.,234,234,2342,22342,22232,17583,9573"
          $ natList

