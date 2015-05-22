module Test.Invariant where

import Test.QuickCheck

infix 1 &>
infix 2 <~~, @~>, <?>, <=>

-- | Defines extensional equality.  This allows concise, point-free,
-- definitions of laws.
--
-- > f(x) == g(x)
-- > f <=> g
(<=>) :: Eq b => (a -> b) -> (a -> b) -> a -> Bool
(f <=> g) x = f x == g x

-- | Pointfree version of QuickChecks ==>.  This notation reduces a
-- lot of lambdas, for example:
--
-- >>> quickCheck $ (/=0) &> not . idempotent (*(2::Int))
-- +++ OK, passed 100 tests.
(&>) :: Testable b => (a -> Bool) -> (a -> b) -> a -> Property
(a &> b) x = a x ==> b x

-- | Checks whether a function is idempotent.
--
-- > f(f(x)) == f(x)
--
-- >>> quickCheck $ idempotent (abs :: Int -> Int)
-- +++ OK, passed 100 tests.
idempotent :: Eq a => (a -> a) -> a -> Bool
idempotent f = f <=> f . f

-- | Checks whether a function is pointSymmetric.
--
-- > f(-x) == -f(x)
--
-- >>> quickCheck $ pointSymmetric (^3)
-- +++ OK, passed 100 tests.
pointSymmetric :: (Num a, Num b, Eq b) => (a -> b) -> a -> Bool
pointSymmetric f = f . negate <=> negate . f

-- | Checks whether a function is reflectionSymmetric.
--
-- > f(x) == f(-x)
--
-- >>> quickCheck $ pointSymmetric (^2)
-- +++ OK, passed 100 tests.
reflectionSymmetric :: (Num a, Eq b) => (a -> b) -> a -> Bool
reflectionSymmetric f = f . negate <=> f

-- | Checks whether a function is monotonicIncreasing.
--
-- > x >= y,  f(x) >= f(y)
--
-- >>> quickCheck $ monotonicIncreasing ceiling
-- +++ OK, passed 100 tests.
monotonicIncreasing :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicIncreasing f x y  = compare (f x) (f y) `elem` [EQ, compare x y]

-- | Checks whether a function is strictly monotonicIncreasing'.
--
-- > x > y,  f(x) > f(y)
--
-- >>> quickCheck $ monotonicIncreasing' (+1)
-- +++ OK, passed 100 tests.
monotonicIncreasing' :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicIncreasing' f x y = compare (f x) (f y) == compare x y

-- | Checks whether a function is monotonicDecreasing.
--
-- > x >= y,  f(x) <= f(y)
--
-- >>> quickCheck $ monotonicDecreasing (\x -> floor $ negate x)
-- +++ OK, passed 100 tests.
monotonicDecreasing :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicDecreasing f x y  = compare (f x) (f y) `elem` [EQ, compare y x]

-- | Checks whether a function is strictly monotonicDecreasing'.
--
-- > x > y,  f(x) < f(y)
--
-- >>> quickCheck $ monotonicDecreasing' (-1)
-- +++ OK, passed 100 tests.
monotonicDecreasing' :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicDecreasing' f x y = compare (f x) (f y) == compare y x

-- TODO create sorted list and fold with predicate over it

-- | Checks whether a function is involutory.
--
-- > f(f(x)) = x
--
-- >>> quickCheck $ involutory negate
-- +++ OK, passed 100 tests.
involutory :: Eq a => (a -> a) -> a -> Bool
involutory f = f . f <=> id

-- | Checks whether a function is the inverse of another function.
--
-- > f(g(x)) = x
--
-- >>> quickCheck $ (`div` 2) `inverts` (*2)
-- +++ OK, passed 100 tests.
inverts :: Eq a => (b -> a) -> (a -> b) -> a -> Bool
f `inverts` g = f . g <=> id

-- | Checks whether an binary operator is commutative.
--
-- > a * b = b * a
--
-- >>> quickCheck $ commutative (+)
-- +++ OK, passed 100 tests.
commutative :: Eq b => (a -> a -> b) -> a -> a -> Bool
commutative f x y = x `f` y == y `f` x

-- | Checks whether an binary operator is associative.
--
-- > a + (b + c) = (a + b) + c
--
-- >>> quickCheck $ associative (+)
-- +++ OK, passed 100 tests.
associative :: Eq a => (a -> a -> a) -> a -> a -> a -> Bool
associative f x y z = x `f` (y `f` z) == (x `f` y) `f` z

-- | Checks whether an operator is left-distributive over an other operator.
--
-- > a * (b + c) = (a * b) + (a * c)
--
-- >>> quickCheck $ (*) `distributesLeftOver` (+)
-- +++ OK, passed 100 tests.
distributesLeftOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
(f `distributesLeftOver` g) x y z = x `f` (y `g` z) == (x `f` y) `g` (x `f` z)

-- | Checks whether an operator is right-distributive over an other operator.
--
-- > (b + c) / a = (b / a) + (c / a)
--
-- >>> quickCheck $ (/) `distributesRightOver` (+)
-- +++ OK, passed 100 tests.
distributesRightOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
(f `distributesRightOver` g) x y z = (y `g` z) `f` x == (x `f` y) `g` (x `f` z)

-- | Checks whether an operator is distributive over an other operator.
--
-- > a * (b + c) = (a * b) + (a * c) = (b + c) * a
--
-- >>> quickCheck $ (*) `distributesOver` (+)
-- +++ OK, passed 100 tests.
distributesOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
(f `distributesOver` g) x y z = (f `distributesLeftOver` g) x y z
                            && (f `distributesRightOver` g) x y z

-- | Checks whether a function increases the size of a list.
--
-- >>> quickCheck $ inflating (1:)
-- +++ OK, passed 100 tests.
inflating :: ([a] -> [b]) -> [a] -> Bool
inflating f xs = length (f xs) >= length xs

-- | Checks whether a function increases strictly the size of a list.
--
-- >>> quickCheck $ inflating (1:)
-- +++ OK, passed 100 tests.
inflating' :: ([a] -> [b]) -> [a] -> Bool
inflating' f xs = length (f xs) > length xs

-- For GHC 7.10
-- inflating :: (Foldable f, Foldable f') => (f a -> f' b) -> f a -> Bool
-- inflating f xs = length (f xs) > length xs

-- | Checks whether a function decreases the size of a list.
--
--
-- >>> quickCheck $ deflating tail
-- +++ OK, passed 100 tests.
deflating :: ([a] -> [b]) -> [a] -> Bool
deflating f xs = length (f xs) <= length xs

-- | Checks whether a function decreases strictly the size of a list.
--
--
-- >>> quickCheck $ deflating tail
-- +++ OK, passed 100 tests.
deflating' :: ([a] -> [b]) -> [a] -> Bool
deflating' f xs = null xs || length (f xs) < length xs

-- For GHC 7.10
-- deflating :: (Foldable f, Foldable f') => (f a -> f' b) -> f a -> Bool
-- deflating f xs = null xs || length (f xs) < length xs

-- | Checks whether a function is cyclic by applying its result to
-- itself within n applications.
--
-- >>> quickCheck $ (`div` 10) `cyclesWithin` 100
-- +++ OK, passed 100 tests.
cyclesWithin :: Eq a => (a -> a) -> Int -> a -> Bool
f `cyclesWithin` n = go [] . take (n + 1) . iterate f
             where go xs (y:ys) | y `elem` xs = True
                                | otherwise   = go (y:xs) ys
                   go _ _ = False

-- | Checks whether a function is invariant over an other function.
--
-- >>> quickCheck $ length `invariatesOver` reverse
-- +++ OK, passed 100 tests.
invariatesOver :: Eq b => (a -> b) -> (a -> a) -> a -> Bool
f `invariatesOver` g = f . g <=> f

-- | Checks whether a binary function is fixed by an argument.
--
-- f x y == const a y
--
-- >>> quickCheck $ (*) `fixedBy` 0
-- +++ OK, passed 100 tests.
fixedBy :: Eq c => (a -> b -> c) -> a -> b -> b -> Bool
(f `fixedBy` x) y z = f x y == f x z

-- | Checks whether a function is invariant over an other function.
--
-- >>> quickCheck $ length <~~ reverse
-- +++ OK, passed 100 tests.
(<~~) :: Eq b => (a -> b) -> (a -> a) -> a -> Bool
f <~~ g = f . g <=> f

-- | Checks whether a function is the inverse of another function.
--
-- > f(g(x)) = x
--
-- >>> quickCheck $ (`div` 2) @~> (*2)
-- +++ OK, passed 100 tests.
(@~>) :: Eq a => (b -> a) -> (a -> b) -> a -> Bool
f @~> g = f . g <=> id

-- | Checks whether a function is an endomorphism in relation to a unary operator.
--
-- > f(g(x)) = g(f(x))
--
-- >>> quickCheck $ (*7) <?> abs
-- +++ OK, passed 100 tests.
(<?>) :: Eq a => (a -> a) -> (a -> a) -> a -> Bool
f <?> g = f . g <=> g . f

-- | Checks whether a function is an endomorphism in relation to a binary operator.
--
-- > f(g(x,y)) = g(f(x),f(y))
--
-- >>> quickCheck $ (^2) <??> (*)
-- +++ OK, passed 100 tests.
(<??>) :: Eq a => (a -> a) -> (a -> a -> a) -> a -> a -> Bool
(f <??> g) x y = f (x `g` y) == f x `g` f y

-- | Checks whether a function is an endomorphism in relation to a ternary operator.
--
-- > f(g(x,y,z)) = g(f(x),f(y),f(z))
--
(<???>) :: Eq a => (a -> a) -> (a -> a -> a -> a) -> a -> a -> a -> Bool
(f <???> g) x y z = f (g x y z) == g (f x) (f y) (f z)
