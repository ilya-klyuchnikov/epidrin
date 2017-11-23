module Utils

import Debug.Trace
import Data.String

%default total
%access public export

track : String -> x -> x
track s = id
--track = trace

copies : Nat -> a -> List a
copies Z x = []
copies (S n) x = x :: (copies n x)

digit : Char -> Maybe Int
digit c = if (isDigit c) then Just ((ord c) - (ord '0')) else Nothing

numeral : String -> Maybe Int
numeral = parseInteger

getLines : IO String
getLines
  = do s <- getLine
       if s == "" then pure ""
                  else do t <- assert_total getLines
                          pure (s ++ "\n" ++ t)

putString : String -> IO ()
putString = putStr

test : Show x => (String -> x) -> IO ()
test cook
  = do s <- getLines
       print (cook s)
