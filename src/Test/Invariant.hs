module Test.Invariant where

infix 0 ===
(===) :: Eq b => (a -> b) -> (a -> b) -> a -> Bool
(f === g) x = f x == g x

idempotent :: Eq a => (a -> a) -> a -> Bool
idempotent f = f === f . f

pointSymmetric :: (Num a, Num b, Eq b) => (a -> b) -> a -> Bool
pointSymmetric f = f . negate === negate . f

reflectionSymmetric :: (Num a, Eq b) => (a -> b) -> a -> Bool
reflectionSymmetric f = f . negate === f

monotonicIncreasing :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicIncreasing f x y  = not $ monotonicDecreasing' f x y

monotonicIncreasing' :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicIncreasing' f x y = compare (f x) (f y) == compare x y

monotonicDecreasing :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicDecreasing f x y  = not $ monotonicIncreasing' f x y

monotonicDecreasing' :: (Ord a, Ord b) => (a -> b) -> a -> a -> Bool
monotonicDecreasing' f x y = compare (f x) (f y) == compare y x

-- TODO create sorted list and fold with predicate over it

involutory :: Eq a => (a -> a) -> a -> Bool
involutory f = f . f === id

inverts :: Eq a => (b -> a) -> (a -> b) -> a -> Bool
f `inverts` g = f . g === id

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
f `cyclesWithin` n = go [] . take (n + 1) . iterate f
             where go xs (y:ys) | y `elem` xs = True
                                | otherwise   = go (y:xs) ys
                   go _ _ = False

scalingInvariant :: (Num a, Eq b) => (a -> a -> b) -> a -> a -> a -> Bool
scalingInvariant f = f `invariatesOver` (*)

translationInvariant :: (Num a, Eq b) => (a -> a -> b) -> a -> a -> a -> Bool
translationInvariant f = f `invariatesOver` (+)

invariatesOver :: Eq b => (a -> a -> b) -> (a -> c -> a) -> a -> a -> c -> Bool
(f `invariatesOver` g) x y z = x `f` y == (x `g` z) `f` (y `g` z)
