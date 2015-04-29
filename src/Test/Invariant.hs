module Test.Invariant where

idempotence :: Eq a => (a -> a) -> a -> Bool
idempotence f x = f x == f (f x)

pointSymmetry :: (Num a, Num b, Eq b) => (a -> b) -> a -> Bool
pointSymmetry f x = f (-x) == - f x

reflectionSymmetry :: (Num a, Eq b) => (a -> b) -> a -> Bool
reflectionSymmetry f x = f (-x) == f x

monotonicIncrease :: (Enum a, Ord b) => (a -> b) -> a -> Bool
monotonicIncrease f x = f x <= f (succ x)

monotonicIncrease' :: (Enum a, Ord b) => (a -> b) -> a -> Bool
monotonicIncrease' f x = f x < f (succ x)

monotonicDecrease :: (Enum a, Ord b) => (a -> b) -> a -> Bool
monotonicDecrease f x = f x >= f (succ x)

monotonicDecrease' :: (Enum a, Ord b) => (a -> b) -> a -> Bool
monotonicDecrease' f x = f x > f (succ x)

inversion :: Eq a => (a -> a) -> a -> Bool
inversion f x = f (f x) == x

commutativity :: Eq b => (a -> a -> b) -> a -> a -> Bool
commutativity f x y = x `f` y == y `f` x

associativity :: Eq a => (a -> a -> a) -> a -> a -> a -> Bool
associativity f x y z = x `f` (y `f` z) == (x `f` y) `f` z

distributesLeftOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
distributesLeftOver f g x y z = x `f` (y `g` z) == (x `f` y) `g` (x `f` z)

distributesRightOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
distributesRightOver f g x y z = (y `g` z) `f` x == (x `f` y) `g` (x `f` z)

distributesOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
distributesOver f g x y z = (f `distributesLeftOver` g) x y z
                            && (f `distributesRightOver` g) x y z
