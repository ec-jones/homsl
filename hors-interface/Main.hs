{-# LANGUAGE BangPatterns #-}

module Main where

import Criterion
import Criterion.Main
import Control.Monad
import System.Directory
import HoMSL.Rewrite
import HoRS.Translation
import HoRS.Syntax
import HoMSL.Syntax
import qualified Data.HashSet as HashSet

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
      bgroup "Bebop/No" [bench bebopNo $ whnf (isNo . saturate) problem
                          | (bebopNo, problem) <- bebopNos
                      ],
      bgroup "Bebop/Yes" [bench bebopYes $ whnf (isYes . saturate) problem
                          | (bebopYes, problem) <- bebopYess
                      ],

      bgroup "Flow/No" [bench flowNo $ whnf (isNo . saturate) problem
                          | (flowNo, problem) <- flowNos
                      ],
      bgroup "Flow/Yes" [bench flowYes $ whnf (isYes . saturate) problem
                          | (flowYes, problem) <- flowYess
                      ],

      bgroup "GTRecS/No" [bench gtrecsNo $ whnf (isNo . saturate) problem
                          | (gtrecsNo, problem) <- gtrecsNos
                      ],
      bgroup "GTRecS/Yes" [bench gtrecsYes $ whnf (isYes . saturate) problem
                          | (gtrecsYes, problem) <- gtrecsYess
                      ],

      bgroup "TRecS/No" [bench trecsNo $ whnf (isNo . saturate) problem
                          | (trecsNo, problem) <- trecsNos
                      ],
      bgroup "TRecS/Yes" [bench trecsYes $ whnf (isYes . saturate) problem
                          | (trecsYes, problem) <- trecsYess
                      ],

      bgroup "HorSat/No" [bench horsatNo $ whnf (isNo . saturate) problem
                          | (horsatNo, problem) <- horsatNos
                      ],
      bgroup "HorSat/Yes" [bench horsatYes $ whnf (isYes . saturate) problem
                          | (horsatYes, problem) <- horsatYess
                      ]
    ]

-- | Verify the output of the benchmark is as expected.
isNo, isYes :: HashSet.HashSet AClause -> ()
isNo cs
  | AClause [] "q0" (Sym "S") (Conj []) `elem` cs =  error "Benchmark failed!"
  | otherwise = ()

isYes cs
  | AClause [] "q0" (Sym "S") (Conj []) `elem` cs = ()
  | otherwise = error "Benchmark failed!"

-- | Read all .hrs problems in a benchmark group.
readBenchmarks :: String -> IO [(FilePath, [Formula])]
readBenchmarks group = do
  problems <- listDirectory ("benchmarks/" ++ group ++ "/")
  forM problems $ \problem -> do
    clauses <- readBenchmark (group ++ "/" ++ problem)
    pure (problem, clauses)

-- | Read a benchmark problem.
readBenchmark :: FilePath -> IO [Formula]
readBenchmark path =  do
  (rules, trans) <- parseHoRS <$> readFile ("benchmarks/" ++ path)
  pure (horsToHoMSL rules trans)

-- | Run a specific benchmark.
runBenchmark :: FilePath -> IO (HashSet.HashSet AClause)
runBenchmark path = do
  input <- readBenchmark path
  pure (saturate input)