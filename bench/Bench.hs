module Main where

import Criterion.Main
import Test.Invariant
import Test.QuickCheck

main :: IO ()
main = defaultMain benchmarks

benchmarks :: [Benchmark]
benchmarks = [ bench "Monotonic" . nfIO . quickCheck $ monotonicIncreasing (*(0::Int)) ]

