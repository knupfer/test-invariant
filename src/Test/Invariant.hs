module Test.Invariant where

idempotent :: Eq a => (a -> a) -> a -> Bool
idempotent f x = f x == f (f x)

pointSymmetric :: (Num a, Num b, Eq b) => (a -> b) -> a -> Bool
pointSymmetric f x = f (-x) == - f x

reflectionSymmetric :: (Num a, Eq b) => (a -> b) -> a -> Bool
reflectionSymmetric f x = f (-x) == f x

monotonicIncreasing :: (Enum a, Ord b) => (a -> b) -> a -> Bool
monotonicIncreasing f x = f x <= f (succ x)

-- TODO create sorted list and fold with predicate over it

monotonicIncreasing' :: (Enum a, Ord b) => (a -> b) -> a -> Bool
monotonicIncreasing' f x = f x < f (succ x)

monotonicDecreasing :: (Enum a, Ord b) => (a -> b) -> a -> Bool
monotonicDecreasing f x = f x >= f (succ x)

monotonicDecreasing' :: (Enum a, Ord b) => (a -> b) -> a -> Bool
monotonicDecreasing' f x = f x > f (succ x)

involutory :: Eq a => (a -> a) -> a -> Bool
involutory f x = f (f x) == x

inverts :: Eq a => (b -> a) -> (a -> b) -> a -> Bool
(f `inverts` g) x = f (g x) == x

commutative :: Eq b => (a -> a -> b) -> a -> a -> Bool
commutative f x y = x `f` y == y `f` x

associative :: Eq a => (a -> a -> a) -> a -> a -> a -> Bool
associative f x y z = x `f` (y `f` z) == (x `f` y) `f` z

distributesLeftOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
(f `distributesLeftOver` g) x y z = x `f` (y `g` z) == (x `f` y) `g` (x `f` z)

distributesRightOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
(f `distributesRightOver` g) x y z = (y `g` z) `f` x == (x `f` y) `g` (x `f` z)

distributesOver :: Eq a => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> Bool
(f `distributesOver` g) x y z = (f `distributesLeftOver` g) x y z
                            && (f `distributesRightOver` g) x y z

inflating :: (Foldable f, Foldable f') => (f a -> f' b) -> f a -> Bool
inflating f xs = length (f xs) > length xs

deflating :: (Foldable f, Foldable f') => (f a -> f' b) -> f a -> Bool
deflating f xs = null xs || length (f xs) < length xs

cyclesWithin :: Eq a => (a -> a) -> Int -> a -> Bool
(f `cyclesWithin` n) x = go [] . take (n + 1) $ iterate f x
             where go xs (y:ys) | y `elem` xs = True
                                | otherwise   = go (y:xs) ys
                   go _ _ = False

scalingInvariant :: (Num a, Eq b) => (a -> a -> b) -> a -> a -> a -> Bool
scalingInvariant f = f `invariatesOver` (*)

translationInvariant :: (Num a, Eq b) => (a -> a -> b) -> a -> a -> a -> Bool
translationInvariant f = f `invariatesOver` (+)

invariatesOver :: Eq b => (a -> a -> b) -> (a -> c -> a) -> a -> a -> c -> Bool
(f `invariatesOver` g) x y z = x `f` y == (x `g` z) `f` (y `g` z)
