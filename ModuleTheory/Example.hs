{-# LANGUAGE GADTs, KindSignatures, ConstraintKinds, StandaloneDeriving, TypeOperators, DataKinds, TypeFamilies, FlexibleInstances #-}
module ModuleTheory.Example where

import Prelude hiding (sum)

import ModuleTheory.Space
import ModuleTheory.Vector
import ModuleTheory.Tick
import ModuleTheory.Intersect
import ModuleTheory.Polyset
import ModuleTheory.Set

cube2 :: Int -> IVec (Copi Int (Copi Int R))
cube2 n = curryCopiProd . mkPolyset . take n $
    concat [concat [[(k, k'), (k', k)] | k' <- [1 .. k - 1]] ++ [(k, k)] | k <- [1 ..]]

cube3 :: Int -> IVec (Copi Int (Copi Int (Copi Int R)))
cube3 n = curryCopiProd . curryCopiProd . mkPolyset . take n $ [((k1, k2), k3) | k1 <- [1 .. nr], k2 <- [1 .. nr], k3 <- [1 .. nr]]
    where
        nr = ceiling (fromIntegral n ** (1 / 3))

caltrop2 :: Int -> IVec (Copi Int (Copi Int R))
caltrop2 n = curryCopiProd . mkPolyset . take n $
    (1, 1) : concat [[(k, 1), (1, k)] | k <- [2 ..]]

caltrop3 :: Int -> IVec (Copi Int (Copi Int (Copi Int R)))
caltrop3 n = curryCopiProd . curryCopiProd . mkPolyset . take n $
    ((1, 1), 1) : concat [[((k, 1), 1), ((1, k), 1), ((1, 1), k)] | k <- [2 ..]]

fin3 :: Int -> IVec (Copi Int (Copi Int (Copi Int R)))
fin3 n = curryCopiProd . curryCopiProd . mkPolyset . take n $
    ((1, 1), 1) : concat [
        [((k, 1), 1), ((1, k), 1), ((1, 1), k)] ++
        concat [[((k, k'), 1), ((k', k), 1), ((k, 1), k'), ((k', 1), k), ((1, k), k'), ((1, k'), k)] | k' <- [2 .. k - 1]] ++
        [((k, k), 1), ((k, 1), k), ((1, k), k)]
        | k <- [2 ..]]

threeCycle impl shape n =
    collect3 . impl (shape n) (shape n) (shape n) $ \a b c -> a * b * c

fourCycle impl shape n =
    collect4 . impl (shape n) (shape n) (shape n) (shape n) $ \a b c d -> a * b * c * d

fourDense impl shape n =
    collect4 . impl (shape n) (shape n) (shape n) (shape n) $ \a b c d -> a * b * c * d

fourTriangles impl shape n =
    collect6 . impl (shape n) (shape n) (shape n) (shape n) (shape n) (shape n) (shape n) (shape n) (shape n) $
    \a b c d e f g h i -> a * b * c * d * e * f * g * h * i

sparseTriangle :: Int -> IVec (Copi Int (Copi Int R))
sparseTriangle n = curryCopiProd . mkPolyset $ [(k, 1) | k <- [1 .. n]] ++ [(1, k) | k <- [2 .. n]]

denseTriangle :: Int -> IVec (Copi Int (Copi Int R))
denseTriangle n = curryCopiProd . mkPolyset $ [(k1, k2) | k1 <- [1 .. n], k2 <- [1 .. n]]

denseFourCycle :: Int -> IVec (Copi Int (Copi Int (Copi Int R)))
denseFourCycle n = curryCopiProd . curryCopiProd . mkPolyset $ [((k1, k2), k3) | k1 <- [1 .. n], k2 <- [1 .. n], k3 <- [1 .. n]]

fastSparseTriangleJoin :: Int -> IVec R
fastSparseTriangleJoin n = collect3 $ intersectThreeCycle x x x $ \a b c -> a * b * c
    where
        m = ceiling $ fromIntegral n / 6
        x = sparseTriangle m

traditionalSparseTriangleJoin :: Int -> IVec R
traditionalSparseTriangleJoin n = collect3 $ traditionalIntersectThreeCycle x x x $ \a b c -> a * b * c
    where
        m = ceiling $ fromIntegral n / 6
        x = sparseTriangle m

fastDenseTriangleJoin :: Int -> IVec R
fastDenseTriangleJoin n = collect3 $ intersectThreeCycle x x x $ \a b c -> a * b * c
    where
        m = ceiling $ sqrt (fromIntegral n / 3)
        x = denseTriangle m

traditionalDenseTriangleJoin :: Int -> IVec R
traditionalDenseTriangleJoin n = collect3 $ traditionalIntersectThreeCycle x x x $ \a b c -> a * b * c
    where
        m = ceiling $ sqrt (fromIntegral n / 3)
        x = denseTriangle m

fastDenseFourCycleJoin :: Int -> IVec R
fastDenseFourCycleJoin n = collect4 $ intersectFourCycle x x x x $ \a b c d -> a * b * c * d
    where
        m = ceiling $ (fromIntegral n / 4) ** (1 / 3)
        x = denseTriangle m

traditionalDenseFourCycleJoin :: Int -> IVec R
traditionalDenseFourCycleJoin n = collect4 $ traditionalIntersectFourCycle x x x x $ \a b c d -> a * b * c * d
    where
        m = ceiling $ (fromIntegral n / 4) ** (1 / 3)
        x = denseTriangle m

{-
fastSparseTriangleJoin :: Int -> IVec R
fastSparseTriangleJoin n = collect . collect . collect $ intersect3 (\a b c -> a * b * c) x x x
    where
        x = sparseTriangle n

denseTriangleJoin :: Int -> IVec R
denseTriangleJoin n = mul3 $ threeWayIntersect' x x x
    where
        x = denseTriangle n

classicalSparseTriangleJoin :: Int -> IVec R
classicalSparseTriangleJoin n = mul3 $ traditionalThreeWayIntersect' t t t -- mul3 . collect . collect . collect $ xyz
    where
        t = sparseTriangle n
        x :: IVec (Copi Int (Copi Int (Pi Int R)))
        x = (use . use . skip $ id) t
        y :: IVec (Copi Int (Pi Int (Copi Int R)))
        y = (use . skip . use $ id) t
        z :: IVec (Pi Int (Copi Int (Copi Int R)))
        z = (skip . use . use $ id) t
        yz = (intersectMany >=| intersectMany >=| intersectMany) (y .*. z)
        xyz = (intersectMany >=| intersectMany >=| intersectMany) (x .*. yz)

classicalDenseTriangleJoin :: Int -> IVec R
classicalDenseTriangleJoin n = mul3 $ traditionalThreeWayIntersect' x x x
    where
        x = denseTriangle n

naiveSparseTriangleJoin :: Int -> IVec R
naiveSparseTriangleJoin n = sum
        [ r1 * r2 * r3
        | ((a, b), r1) <- x
        , ((a', c), r2) <- x
        , a == a'
        , ((b', c'), r3) <- x
        , b == b'
        , c == c'
        ]
    where
        x = [((a, b), r) | (a, v) <- decomposeCoprod (sparseTriangle n), (b, r) <- decomposeCoprod v]

{-
classicalSparseTriangleJoin :: Int -> IVec R
classicalSparseTriangleJoin n = sum
        [ r1 * r2 * r3
        | ((a, b), r1) <- x
        , c <- [1 .. if a == 1 then n else 1]
        , let r2 = 1
        , ((b', c'), r3) <- x
        , b == b'
        , c == c'
        ]
    where
        x = [((a, b), r) | (a, v) <- decomposeCoprod (sparseTriangle n), (b, r) <- decomposeCoprod v]
-}

x :: Vec Int (Copi Char (Copi Char R))
x = curryCopiProd . mkPolyset $
    [('a', 'k')
    ,('a', 'm')
    ,('b', 'k')
    ,('b', 'm')
    ]

y :: Vec Int (Copi Char (Copi Char R))
y = curryCopiProd . mkPolyset $
    [('a', 'p')
    ]
z :: Vec Int (Copi Char (Copi Char R))
z = curryCopiProd . mkPolyset $
    [('k', 'p')
    ]

xyz = threeWayIntersect' x y z
-}
