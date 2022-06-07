module Main where

import Control.Monad
import Parser
import Resolve

main :: IO ()
main = do
  input <- parseProgram <$> readFile "input/partial"
  forM_ (saturate input) $ \cls -> do
    print cls
