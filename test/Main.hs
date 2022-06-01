module Main where

import Resolve
import Parser

main :: IO ()
main = do
  input <- parseProgram <$> readFile "input/partial"
  print (saturate input)