{-# LANGUAGE BangPatterns #-}

module Main where

import Criterion
import Criterion.Main
import Control.Monad
import System.Directory
import qualified HoMSL.ClauseSet as ClauseSet
import HoMSL.Rewrite
import HoRS.Translation
import HoRS.Syntax
import HoMSL.Syntax
import Control.DeepSeq
import Debug.Trace

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
      bgroup "Bebop/No" [bench bebopNo $ whnf (isNo . runBenchmark) problem
                          | (bebopNo, problem) <- bebopNos
                      ],
      bgroup "Bebop/Yes" [bench bebopYes $ whnf (isYes . runBenchmark) problem
                          | (bebopYes, problem) <- bebopYess
                      ],

      bgroup "Flow/No" [bench flowNo $ whnf (isNo . runBenchmark) problem
                          | (flowNo, problem) <- flowNos
                      ],
      bgroup "Flow/Yes" [bench flowYes $ whnf (isYes . runBenchmark) problem
                          | (flowYes, problem) <- flowYess
                      ],

      bgroup "GTRecS/No" [bench gtrecsNo $ whnf (isNo . runBenchmark) problem
                          | (gtrecsNo, problem) <- gtrecsNos
                      ],
      bgroup "GTRecS/Yes" [bench gtrecsYes $ whnf (isYes . runBenchmark) problem
                          | (gtrecsYes, problem) <- gtrecsYess
                      ],

      bgroup "TRecS/No" [bench trecsNo $ whnf (isNo . runBenchmark) problem
                          | (trecsNo, problem) <- trecsNos
                      ],
      bgroup "TRecS/Yes" [bench trecsYes $ whnf (isYes . runBenchmark) problem
                          | (trecsYes, problem) <- trecsYess
                      ],

      bgroup "HorSat/No" [bench horsatNo $ whnf (isNo . runBenchmark) problem
                          | (horsatNo, problem) <- horsatNos
                      ],
      bgroup "HorSat/Yes" [bench horsatYes $ whnf (isYes . runBenchmark) problem
                          | (horsatYes, problem) <- horsatYess
                      ]
    ]

-- | Verify the output of the benchmark is as expected.
isNo, isYes :: Bool -> ()
isNo True = ()
isNo False = error "Benchmark failed!"

isYes False = ()
isYes True = error "Benchmark failed!"

-- | Run a specific benchmark.
runBenchmark :: ClauseSet.ClauseSet -> Bool
runBenchmark input = 
  rewrite input $ Atom $ App (Sym "q0") (Sym "S")

-- | Read all .hrs problems in a benchmark group.
readBenchmarks :: String -> IO [(FilePath, ClauseSet.ClauseSet)]
readBenchmarks group = do
  problems <- listDirectory ("benchmarks/" ++ group ++ "/")
  problems <- forM problems $ \problem -> do
    clauses <- readBenchmark (group ++ "/" ++ problem)
    pure (problem, clauses)
  pure (force problems)

-- | Read a benchmark problem.
readBenchmark :: FilePath -> IO (ClauseSet.ClauseSet)
readBenchmark path =  do
  (rules, trans) <- parseHoRS <$> readFile ("benchmarks/" ++ path)
  pure (horsToHoMSL rules trans)