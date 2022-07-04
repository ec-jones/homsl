{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Criterion
import Criterion.Main
import Control.Monad
import System.Directory
import HoMSL.Rewrite
import HoRS.Translation
import HoRS.Syntax
import System.CPUTime
import System.Timeout
import HoMSL.Syntax
import qualified Data.HashSet as HashSet

main :: IO ()
main = do
  -- group <- readBenchmarks "Bebop/No"
  -- forM_ group $ \(problem, (s, clauses)) -> do
  --   putStrLn problem
  --   time (isNo s $ saturate (s, clauses)) >>= \case
  --     Nothing -> putStrLn "Time out!"
  --     Just dt -> putStrLn ("Time: " ++ show dt) 
    
  -- group <- readBenchmarks "Bebop/Yes"
  -- forM_ group $ \(problem, (s, clauses)) -> do
  --   putStrLn problem
  --   time (isYes s $ saturate (s, clauses)) >>= \case
  --     Nothing -> putStrLn "Time out!"
  --     Just dt -> putStrLn ("Time: " ++ show dt)

  -- group <- readBenchmarks "Flow/No"
  -- forM_ group $ \(problem, (s, clauses)) -> do
  --   putStrLn problem
  --   time (isNo s $ saturate (s, clauses)) >>= \case
  --     Nothing -> putStrLn "Time out!"
  --     Just dt -> putStrLn ("Time: " ++ show dt) 

  -- group <- readBenchmarks "Flow/Yes"
  -- forM_ group $ \(problem, (s, clauses)) -> do
  --   putStrLn problem
  --   time (isYes s $ saturate (s, clauses)) >>= \case
  --     Nothing -> putStrLn "Time out!"
  --     Just dt -> putStrLn ("Time: " ++ show dt) 

  -- group <- readBenchmarks "GTRecS/No"
  -- forM_ group $ \(problem, (s, clauses)) -> do
  --   putStrLn problem
  --   time (isNo s $ saturate (s, clauses)) >>= \case
  --     Nothing -> putStrLn "Time out!"
  --     Just dt -> putStrLn ("Time: " ++ show dt) 

  -- group <- readBenchmarks "GTRecS/Yes"
  -- forM_ group $ \(problem, (s, clauses)) -> do
  --   putStrLn problem
  --   time (isYes s $ saturate (s, clauses)) >>= \case
  --     Nothing -> putStrLn "Time out!"
  --     Just dt -> putStrLn ("Time: " ++ show dt) 

  -- group <- readBenchmarks "TRecS/No"
  -- forM_ group $ \(problem, (s, clauses)) -> do
  --   putStrLn problem
  --   time (isNo s $ saturate (s, clauses)) >>= \case
  --     Nothing -> putStrLn "Time out!"
  --     Just dt -> putStrLn ("Time: " ++ show dt) 

  -- group <- readBenchmarks "TRecS/Yes"
  -- forM_ group $ \(problem, (s, clauses)) -> do
  --   putStrLn problem
  --   time (isYes s $ saturate (s, clauses)) >>= \case
  --     Nothing -> putStrLn "Time out!"
  --     Just dt -> putStrLn ("Time: " ++ show dt)

  group <- readBenchmarks "HorSat/No"
  forM_ group $ \(problem, (s, clauses)) -> do
    putStrLn problem
    time (isNo s $ saturate (s, clauses)) >>= \case
      Nothing -> putStrLn "Time out!"
      Just dt -> putStrLn ("Time: " ++ show dt) 

  group <- readBenchmarks "HorSat/Yes"
  forM_ group $ \(problem, (s, clauses)) -> do
    putStrLn problem
    time (isYes s $ saturate (s, clauses)) >>= \case
      Nothing -> putStrLn "Time out!"
      Just dt -> putStrLn ("Time: " ++ show dt)  

-- | Verify the output of the benchmark is as expected.
isNo, isYes :: String -> HashSet.HashSet AClause -> IO ()
isNo s cs
  | AClause [] "q0" (Sym s) (Conj []) `elem` cs = pure ()
  | otherwise =  putStrLn "Benchmark failed!"

isYes s cs
  | AClause [] "q0" (Sym s) (Conj []) `elem` cs = putStrLn "Benchmark failed!"
  | otherwise = pure ()

-- | Read all .hrs problems in a benchmark group.
readBenchmarks :: String -> IO [(FilePath, (String, [Formula]))]
readBenchmarks group = do
  problems <- listDirectory ("benchmarks/" ++ group ++ "/")
  forM problems $ \problem -> do
    (s, clauses) <- readBenchmark (group ++ "/" ++ problem)
    pure (group ++ "/" ++ problem, (s, clauses))

-- | Read a benchmark problem.
readBenchmark :: FilePath -> IO (String, [Formula])
readBenchmark path =  do
  (rules, trans) <- parseHoRS <$> readFile ("benchmarks/" ++ path)
  pure (horsToHoMSL rules trans)

-- | Run a specific benchmark (for interactive use).
runBenchmark :: FilePath -> IO (HashSet.HashSet AClause)
runBenchmark path = do
  input <- readBenchmark path
  pure (saturate input)

-- * Timing facilities

time :: IO () -> IO (Maybe Float)
time m = do
  !t0 <- getCPUTime 
  !res <- timeout (10 * 1000000) m
  !t1 <- getCPUTime
  pure (fromIntegral (t1 - t0) / 10000000000.0 <$ res)