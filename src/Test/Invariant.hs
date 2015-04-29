module Test.Invariant where

idempotence :: Eq a => (a -> a) -> a -> Bool
idempotence f x = f x == f (f x)

pointSymmetry :: (Num a, Num b, Eq b) => (a -> b) -> a -> Bool
pointSymmetry f x = f (-x) == - f x

reflectionSymmetry :: (Num a, Eq b) => (a -> b) -> a -> Bool
reflectionSymmetry f x = f (-x) == f x

monotonicIncrease :: (Enum a, Ord b) => (a -> b) -> a -> Bool
monotonicIncrease f x = f x <= f (succ x)

monotonicDecrease :: (Enum a, Ord b) => (a -> b) -> a -> Bool
monotonicDecrease f x = f x >= f (succ x)
