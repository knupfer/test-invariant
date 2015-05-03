module Main where

import Test.Invariant
import Test.Tasty
import Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain $
  testGroup "Tests"
    [ testGroup "Arity 1"
      [ testProperty "Idempotence" $
        idempotent (* (0 :: Int))

      , testProperty "Idempotence" $
        (/=0) &> not . idempotent (* (2 :: Int))

      , testProperty "Idempotence" $
        idempotent (abs :: Double -> Double)

      , testProperty "Idempotence" $
        idempotent (signum :: Int -> Int)

      , testProperty "Idempotence" $
        ((*) :: Int -> Int -> Int) `distributesOver` (+)

      , testProperty "Idempotence" $
        (*) `distributesOver` ((+) :: Int -> Int -> Int)
      ]
    ]


