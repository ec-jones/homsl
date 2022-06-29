{-# LANGUAGE BangPatterns #-}

module Main where

import Criterion
import Criterion.Main
import Control.Monad
import System.Directory
import HoMSL.Resolve
import HoRS.Translation
import HoRS.Syntax
import Control.DeepSeq
import HoMSL.Syntax

main :: IO ()
main = do
  -- Preload HoMSL problems.
  !bebopNos <- readBenchmarks "Bebop/No"
  !bebopYess <- readBenchmarks "Bebop/Yes"
  
  !flowNos <- readBenchmarks "Flow/No"
  !flowYess <- readBenchmarks "Flow/Yes"

  !gtrecsNos <- readBenchmarks "GTRecS/No"
  !gtrecsYess <- readBenchmarks "GTRecS/Yes"

  !trecsNos <- readBenchmarks "TRecS/No"
  !trecsYess <- readBenchmarks "TRecS/Yes"

  !horsatNos <- readBenchmarks "HorSat/No"
  !horsatYess <- readBenchmarks "HorSat/Yes"

  -- Benchmark groups
  defaultMain [
      bgroup "Bebop" [bench bebopNo $ whnf (isNo . saturate) problem
                          | (bebopNo, problem) <- bebopNos
                      ],
      bgroup "Bebop" [bench bebopYes $ whnf (isYes . saturate) problem
                          | (bebopYes, problem) <- bebopYess
                      ],

      bgroup "Flow" [bench flowNo $ whnf (fst . saturate) problem
                          | (flowNo, problem) <- flowNos
                      ],
      bgroup "Flow" [bench flowYes $ whnf (fst . saturate) problem
                          | (flowYes, problem) <- flowYess
                      ],

      bgroup "GTRecS" [bench gtrecsNo $ whnf (fst . saturate) problem
                          | (gtrecsNo, problem) <- gtrecsNos
                      ],
      bgroup "GTRecS" [bench gtrecsYes $ whnf (fst . saturate) problem
                          | (gtrecsYes, problem) <- gtrecsYess
                      ],

      bgroup "TRecS" [bench trecsNo $ whnf (fst . saturate) problem
                          | (trecsNo, problem) <- trecsNos
                      ],
      bgroup "TRecS" [bench trecsYes $ whnf (fst . saturate) problem
                          | (trecsYes, problem) <- trecsYess
                      ],

      bgroup "HorSat" [bench horsatNo $ whnf (fst . saturate) problem
                          | (horsatNo, problem) <- horsatNos
                      ],
      bgroup "HorSat" [bench horsatYes $ whnf (fst . saturate) problem
                          | (horsatYes, problem) <- horsatYess
                      ]
    ]

isNo, isYes :: (Bool, a) -> ()
isNo (True, _) = ()
isNo (False, _) = error "Problem failed!"

isYes (False, _) = ()
isYes (True, _) = error "Problem failed!"

-- | Read all .hrs problems in a benchmark group.
readBenchmarks :: String -> IO [(FilePath, ClauseSet Formula)]
readBenchmarks group = do
  problems <- listDirectory ("benchmarks/" ++ group ++ "/")
  problems <- forM problems $ \problem -> do
    (rules, trans) <- parseHoRS <$> readFile ("benchmarks/" ++ group ++ "/" ++ problem)
    pure (problem, horsToHoMSL rules trans)
  pure (force problems)