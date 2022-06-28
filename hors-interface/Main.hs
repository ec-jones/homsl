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
main = undefined -- do
--   -- Preload HoMSL problems.
--   !bebopNos <- readBenchmarks "Bebop/No"
--   !bebopYess <- readBenchmarks "Bebop/Yes"
  
--   !flowNos <- readBenchmarks "Flow/No"
--   !flowYess <- readBenchmarks "Flow/Yes"

--   !gtrecsNos <- readBenchmarks "GTRecS/No"
--   !gtrecsYess <- readBenchmarks "GTRecS/Yes"

--   !trecsNos <- readBenchmarks "TRecS/No"
--   !trecsYess <- readBenchmarks "TRecS/Yes"

--   !horsatNos <- readBenchmarks "HorSat/No"
--   !horsatYess <- readBenchmarks "HorSat/Yes"

--   -- Benchmark groups
--   defaultMain [
--       bgroup "Bebop" [bench bebopNo $ whnf (isNo . satisfiable) problem
--                           | (bebopNo, problem) <- bebopNos
--                       ],
--       bgroup "Bebop" [bench bebopYes $ whnf (isYes . satisfiable) problem
--                           | (bebopYes, problem) <- bebopYess
--                       ],

--       bgroup "Flow" [bench flowNo $ whnf (isNo . satisfiable) problem
--                           | (flowNo, problem) <- flowNos
--                       ],
--       bgroup "Flow" [bench flowYes $ whnf (isYes . satisfiable) problem
--                           | (flowYes, problem) <- flowYess
--                       ],

--       bgroup "GTRecS" [bench gtrecsNo $ whnf (isNo . satisfiable) problem
--                           | (gtrecsNo, problem) <- gtrecsNos
--                       ],
--       bgroup "GTRecS" [bench gtrecsYes $ whnf (isYes . satisfiable) problem
--                           | (gtrecsYes, problem) <- gtrecsYess
--                       ],

--       bgroup "TRecS" [bench trecsNo $ whnf (isNo . satisfiable) problem
--                           | (trecsNo, problem) <- trecsNos
--                       ],
--       bgroup "TRecS" [bench trecsYes $ whnf (isYes . satisfiable) problem
--                           | (trecsYes, problem) <- trecsYess
--                       ],

--       bgroup "HorSat" [bench horsatNo $ whnf (isNo . satisfiable) problem
--                           | (horsatNo, problem) <- horsatNos
--                       ],
--       bgroup "HorSat" [bench horsatYes $ whnf (isYes . satisfiable) problem
--                           | (horsatYes, problem) <- horsatYess
--                       ]
--     ]

-- | Verify the output of the benchmark is as expected.
isNo, isYes :: (Bool, a) -> ()
isNo (True, _) = ()
isNo (False, _) = error "Benchmark failed!"

isYes (False, _) = ()
isYes (True, _) = error "Benchmark failed!"

-- | Run a specific benchmark.
runBenchmark :: FilePath -> IO [Formula]
runBenchmark path = do
  input <- readBenchmark path
  pure (rewrite input (Atom (App (Sym "q0") (Sym "S"))))

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