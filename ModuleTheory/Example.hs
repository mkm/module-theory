{-# LANGUAGE GADTs, KindSignatures, ConstraintKinds, StandaloneDeriving, TypeOperators, DataKinds, TypeFamilies, FlexibleInstances #-}
module ModuleTheory.Example where

import Prelude hiding (sum)

import ModuleTheory.Space
import ModuleTheory.Vector
import ModuleTheory.Tick
import ModuleTheory.Intersect
import ModuleTheory.Polyset
import ModuleTheory.Set

cube2 :: Int -> IVec (Int :=> Int :=> R)
cube2 n = curryCopowProd . mkPolyset . take n $
    concat [concat [[(k, k'), (k', k)] | k' <- [1 .. k - 1]] ++ [(k, k)] | k <- [1 ..]]

cube3 :: Int -> IVec (Int :=> Int :=> Int :=> R)
cube3 n = curryCopowProd . curryCopowProd . mkPolyset . take n $ [((k1, k2), k3) | k1 <- [1 .. nr], k2 <- [1 .. nr], k3 <- [1 .. nr]]
    where
        nr = ceiling (fromIntegral n ** (1 / 3))

caltrop2 :: Int -> IVec (Int :=> Int :=> R)
caltrop2 n = curryCopowProd . mkPolyset . take n $
    (1, 1) : concat [[(k, 1), (1, k)] | k <- [2 ..]]

caltrop3 :: Int -> IVec (Int :=> Int :=> Int :=> R)
caltrop3 n = curryCopowProd . curryCopowProd . mkPolyset . take n $
    ((1, 1), 1) : concat [[((k, 1), 1), ((1, k), 1), ((1, 1), k)] | k <- [2 ..]]

fin3 :: Int -> IVec (Int :=> Int :=> Int :=> R)
fin3 n = curryCopowProd . curryCopowProd . mkPolyset . take n $
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

sparseTriangle :: Int -> IVec (Int :=> Int :=> R)
sparseTriangle n = curryCopowProd . mkPolyset $ [(k, 1) | k <- [1 .. n]] ++ [(1, k) | k <- [2 .. n]]

denseTriangle :: Int -> IVec (Int :=> Int :=> R)
denseTriangle n = curryCopowProd . mkPolyset $ [(k1, k2) | k1 <- [1 .. n], k2 <- [1 .. n]]

denseFourCycle :: Int -> IVec (Int :=> Int :=> Int :=> R)
denseFourCycle n = curryCopowProd . curryCopowProd . mkPolyset $ [((k1, k2), k3) | k1 <- [1 .. n], k2 <- [1 .. n], k3 <- [1 .. n]]

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
