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
main = pure () -- do
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
--       bgroup "Bebop/No" [bench bebopNo $ whnf (isNo . satisfiable) problem
--                           | (bebopNo, problem) <- bebopNos
--                       ],
--       bgroup "Bebop/Yes" [bench bebopYes $ whnf (isYes . satisfiable) problem
--                           | (bebopYes, problem) <- bebopYess
--                       ],

--       bgroup "Flow/No" [bench flowNo $ whnf (isNo . satisfiable) problem
--                           | (flowNo, problem) <- flowNos
--                       ],
--       bgroup "Flow/Yes" [bench flowYes $ whnf (isYes . satisfiable) problem
--                           | (flowYes, problem) <- flowYess
--                       ],

--       bgroup "GTRecS/No" [bench gtrecsNo $ whnf (isNo . satisfiable) problem
--                           | (gtrecsNo, problem) <- gtrecsNos
--                       ],
--       bgroup "GTRecS/Yes" [bench gtrecsYes $ whnf (isYes . satisfiable) problem
--                           | (gtrecsYes, problem) <- gtrecsYess
--                       ],

--       bgroup "TRecS/No" [bench trecsNo $ whnf (isNo . satisfiable) problem
--                           | (trecsNo, problem) <- trecsNos
--                       ],
--       bgroup "TRecS/Yes" [bench trecsYes $ whnf (isYes . satisfiable) problem
--                           | (trecsYes, problem) <- trecsYess
--                       ],

--       bgroup "HorSat/No" [bench horsatNo $ whnf (isNo . satisfiable) problem
--                           | (horsatNo, problem) <- horsatNos
--                       ],
--       bgroup "HorSat/Yes" [bench horsatYes $ whnf (isYes . satisfiable) problem
--                           | (horsatYes, problem) <- horsatYess
--                       ]
--     ]

-- -- | Verify the output of the benchmark is as expected.
-- isNo, isYes :: Bool -> ()
-- isNo False = ()
-- isNo True = error "Benchmark failed!"

-- isYes True = ()
-- isYes False = error "Benchmark failed!"

-- | Run a specific benchmark.
runBenchmark :: FilePath -> IO Bool
runBenchmark path = do
  input <- readBenchmark path
  pure (satisfiable input)

satisfiable :: ClauseSet.ClauseSet -> Bool
satisfiable cs = 
  Atom (App (Sym "q0") (Sym "S")) 
    `elem` saturateClauses cs "q0"

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