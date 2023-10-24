module NameWrangler
  ( upperSnakeCase
  , lowerSnakeCase
  , mkName
  ) where

import Data.Char (isAlpha, isDigit, isUpper, toLower, toUpper)
import Data.List (groupBy, intercalate)
import Data.List.Split (condense, dropInitBlank, keepDelimsL, split, splitOn, whenElt)

snakeCase :: String -> String
snakeCase str = intercalate "_" . groupSingles $ (split . keepDelimsL . dropInitBlank . whenElt) isUpper =<< splitDigit =<< splitOn "_" str
 where
  splitDigit = (split . condense . whenElt) isDigit
  groupSingles = map concat . groupBy singles
   where
    singles [x] [y] = isAlpha x && isAlpha y
    singles _ _ = False

upperSnakeCase :: String -> String
upperSnakeCase = map toUpper . snakeCase

lowerSnakeCase :: String -> String
lowerSnakeCase = map toLower . snakeCase

mkName :: Show a => a -> String
mkName = filter (`notElem` "()") . last . words . show

