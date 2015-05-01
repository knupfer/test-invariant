module Test.Invariant where

import Test.QuickCheck
infix 1 <=>, &>

-- | Defines extensional equality.  This allows concise, point-free,
-- definitions of laws.  For example idempotence: f <=> f . f
(<=>) :: Eq b => (a -> b) -> (a -> b) -> a -> Bool
(f <=> g) x = f x == g x

-- | Pointfree version of QuickChecks ==>.  This notation reduces a
-- lot of lambdas, for example:
-- quickCheck $ (/=0) &> not . idempotent (*(2::Int))
(&>) :: Testable b => (a -> Bool) -> (a -> b) -> a -> Property
(a &> b) x = a x ==> b x

-- | Checks whether a function is idempotent.
-- f(f(x)) == f(x)
idempotent :: Eq a => (a -> a) -> a -> Bool
idempotent f = f <=> f . f

-- | Checks whether a function is pointSymmetric.
-- f(-x) == -f(x)
pointSymmetric :: (Num a, Num b, Eq b) => (a -> b) -> a -> Bool
pointSymmetric f = f . negate <=> negate . f

-- | Checks whether a function is reflectionSymmetric.
-- f(x) == f(-x)
reflectionSymmetric :: (Num a, Eq b) => (a -> b) -> a -> Bool
reflectionSymmetric f = f . negate <=> f

-- | Checks whether a function is monotonicIncreasing.
-- x >= y,  f(x) >= f(y)
monotonicIncreasing :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicIncreasing f x y  = not $ monotonicDecreasing' f x y

-- | Checks whether a function is strictly monotonicIncreasing'.
-- x > y,  f(x) > f(y)
monotonicIncreasing' :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicIncreasing' f x y = compare (f x) (f y) == compare x y

-- | Checks whether a function is monotonicDecreasing.
-- x >= y,  f(x) <= f(y)
monotonicDecreasing :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicDecreasing f x y  = not $ monotonicIncreasing' f x y

-- | Checks whether a function is strictly monotonicDecreasing'.
-- x > y,  f(x) < f(y)
monotonicDecreasing' :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicDecreasing' f x y = compare (f x) (f y) == compare y x

-- TODO create sorted list and fold with predicate over it

-- | Checks whether a function is involutory.
-- f(f(x)) = x
involutory :: Eq a => (a -> a) -> a -> Bool
involutory f = f . f <=> id

-- | Checks whether a function is the inverse of another function.
-- f(g(x)) = x
inverts :: Eq a => (b -> a) -> (a -> b) -> a -> Bool
f `inverts` g = f . g <=> id

-- | Checks whether an binary operator is commutative.
-- a * b = b * a
commutative :: Eq b => (a -> a -> b) -> a -> a -> Bool
commutative f x y = x `f` y == y `f` x

-- | Checks whether an binary operator is associative.
-- a + (b + c) = (a + b) + c
associative :: Eq a => (a -> a -> a) -> a -> a -> a -> Bool
associative f x y z = x `f` (y `f` z) == (x `f` y) `f` z

-- | Checks whether an operator is left-distributive over an other operator.
-- a * (b + c) = (a * b) + (a * c)
distributesLeftOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
(f `distributesLeftOver` g) x y z = x `f` (y `g` z) == (x `f` y) `g` (x `f` z)

-- | Checks whether an operator is right-distributive over an other operator.
-- (b + c) / a = (b / a) + (c / a)
distributesRightOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
(f `distributesRightOver` g) x y z = (y `g` z) `f` x == (x `f` y) `g` (x `f` z)

-- | Checks whether an operator is distributive over an other operator.
-- a * (b + c) = (a * b) + (a * c) = (b + c) * a
distributesOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
(f `distributesOver` g) x y z = (f `distributesLeftOver` g) x y z
                            && (f `distributesRightOver` g) x y z

-- | Checks whether a function increases the size of a foldable.
inflating :: (Foldable f, Foldable f') => (f a -> f' b) -> f a -> Bool
inflating f xs = length (f xs) > length xs

-- | Checks whether a function decreases the size of a foldable.
deflating :: (Foldable f, Foldable f') => (f a -> f' b) -> f a -> Bool
deflating f xs = null xs || length (f xs) < length xs

-- | Checks whether a function is cyclic by applying its result to
-- itself within n applications.
cyclesWithin :: Eq a => (a -> a) -> Int -> a -> Bool
f `cyclesWithin` n = go [] . take (n + 1) . iterate f
             where go xs (y:ys) | y `elem` xs = True
                                | otherwise   = go (y:xs) ys
                   go _ _ = False

-- | Checks whether a function is invariant over an other function.
-- sort `invariatesOver` reverse
invariatesOver :: Eq b => (a -> b) -> (a -> a) -> a -> Bool
f `invariatesOver` g = f . g <=> f
