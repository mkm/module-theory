{-# LANGUAGE GADTs, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances, TypeFamilies, TypeOperators, DataKinds, KindSignatures #-}
module ModuleTheory.Intersect (
        Algebra(..),
        intersect2,
        intersect3,
        intersectThreeCycle,
        traditionalIntersectThreeCycle,
        intersectFourCycle,
        traditionalIntersectFourCycle,
        intersectFourDense,
        traditionalIntersectFourDense,
        intersectFourTriangles,
        traditionalIntersectFourTriangles,
    ) where

import ModuleTheory.Space
import ModuleTheory.Vector
import ModuleTheory.Tick

class Algebra v where
    intersect :: Ring r => Vec r v -> Vec r v -> Vec r v

class Algebra v => UnitalAlgebra v where
    unit :: Ring r => Vec r v

instance (Ring r, UnitalAlgebra v) => Num (Vec r v) where
    fromInteger n = fromInteger n *. unit
    (+) = (.+.)
    negate = (*) (-1)
    (*) = intersect
    abs = id
    signum _ = 1

instance Algebra R where
    intersect x y = mkScalar $ getScalar x * getScalar y

instance UnitalAlgebra R where
    unit = mkScalar 1

instance (FirstOrder a, Algebra v) => Algebra (Copow a v) where
    intersect = intersectCopow (const intersect)

instance (FirstOrder a, Algebra v) => Algebra (CCopow a v) where
    intersect = bilinear $ \(AdjoinUnit u1 v1) (AdjoinUnit u2 v2) ->
        Gen $ AdjoinUnit (intersect u1 u2) (intersect v1 v2 .+. mapCopow (const (`intersect` u2)) v1 .+. mapCopow (const (u1 `intersect`)) v2)

instance (FirstOrder a, UnitalAlgebra v) => UnitalAlgebra (CCopow a v) where
    unit = Gen $ AdjoinUnit 1 zero

instance Algebra v => Algebra (Pow a v) where
    intersect u v = powExt $ \a -> intersect (appPow u a) (appPow v a)

instance UnitalAlgebra v => UnitalAlgebra (Pow a v) where
    unit = powExt $ const unit

instance (Algebra u, Algebra v) => Algebra (u :+: v) where
    intersect = bilinear $ \(DirectSum u1 v1) (DirectSum u2 v2) -> Gen $ DirectSum (intersect u1 u2) (intersect v1 v2)

instance (UnitalAlgebra u, UnitalAlgebra v) => UnitalAlgebra (u :+: v) where
    unit = Gen $ DirectSum unit unit

instance (Algebra u, Algebra v) => Algebra (u :*: v) where
    intersect = bilinear $ \(Tensor u1 v1) (Tensor u2 v2) -> intersect u1 u2 .*. intersect v1 v2

instance (UnitalAlgebra u, UnitalAlgebra v) => UnitalAlgebra (u :*: v) where
    unit = unit .*. unit

intersect2 :: (Ring r, FirstOrder a) => Vec r (Copow a u1) -> Vec r (Copow a u2) -> (Vec r u1 -> Vec r u2 -> Vec r v) -> Vec r (Copow a v)
intersect2 u1 u2 f = tick $ intersectCopow (\_ x y -> tick $ f x y) u1 u2

intersect2' :: (Ring r, FirstOrder a) => Vec r (Copow a u1) -> Vec r (Copow a u2) -> (a -> Vec r u1 -> Vec r u2 -> Vec r v) -> Vec r (Copow a v)
intersect2' u1 u2 f = tick $ intersectCopow (\a x y -> tick $ f a x y) u1 u2

intersect3 :: (Ring r, FirstOrder a) =>
    Vec r (Copow a u1) -> Vec r (Copow a u2) -> Vec r (Copow a u3) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r v) ->
    Vec r (Copow a v)
intersect3 u1 u2 u3 f = intersect2 u1 (intersect2 u2 u3 (.*.)) $ \x1 -> tensorExt $ \x2 x3 -> f x1 x2 x3

intersect4 :: (Ring r, FirstOrder a) =>
    Vec r (Copow a u1) -> Vec r (Copow a u2) -> Vec r (Copow a u3) -> Vec r (Copow a u4) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copow a v)
intersect4 u1 u2 u3 u4 f = intersect2 u1 (intersect3 u2 u3 u4 tensor3) $ \x1 -> tensorExt $ \x2 -> tensorExt $ \x3 x4 -> f x1 x2 x3 x4

intersectThreeCycle :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c) => 
    Vec r (Copow a (Copow b u1)) ->
    Vec r (Copow a (Copow c u2)) ->
    Vec r (Copow b (Copow c u3)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r v) ->
    Vec r (Copow a (Copow b (Copow c v)))
intersectThreeCycle x y z f =
    intersect2 x y $ \x' y' ->
    intersect2 x' z $ \x'' z' ->
    intersect2 y' z' $ \y'' z'' ->
    f x'' y'' z''

traditionalIntersectThreeCycle :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c) => 
    Vec r (Copow a (Copow b u1)) ->
    Vec r (Copow a (Copow c u2)) ->
    Vec r (Copow b (Copow c u3)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r v) ->
    Vec r (Copow a (Copow b (Copow c v)))
traditionalIntersectThreeCycle x y z f =
    intersect2 x y $ \x' y' ->
    let w = materialiseProduct x' y' in
    intersect2 w z $ \w' z' ->
    intersect2 w' z' $ \w'' z'' ->
    tensorExt (\x'' y'' -> f x'' y'' z'') w''

intersectFourCycle :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d) => 
    Vec r (Copow a (Copow b u1)) ->
    Vec r (Copow b (Copow c u2)) ->
    Vec r (Copow c (Copow d u3)) ->
    Vec r (Copow a (Copow d u4)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copow a (Copow b (Copow c (Copow d v))))
intersectFourCycle x y z w f =
    intersect2 x w $ \x' w' ->
    intersect2 x' y $ \x'' y' ->
    intersect2 y' z $ \y'' z' ->
    intersect2 z' w' $ \z'' w'' ->
    f x'' y'' z'' w''

traditionalIntersectFourCycle :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d) => 
    Vec r (Copow a (Copow b u1)) ->
    Vec r (Copow b (Copow c u2)) ->
    Vec r (Copow c (Copow d u3)) ->
    Vec r (Copow a (Copow d u4)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copow a (Copow b (Copow c (Copow d v))))
traditionalIntersectFourCycle x y z w f =
    intersect2 x w $ \x' w' ->
    let p = materialiseProduct x' w' in
    traditionalIntersectThreeCycle y p z $ \y'' p'' z'' ->
    tensorExt (\x'' w'' -> f x'' y'' z'' w'') p''

intersectFourDense :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d) => 
    Vec r (Copow a (Copow b (Copow c u1))) ->
    Vec r (Copow a (Copow b (Copow d u2))) ->
    Vec r (Copow a (Copow c (Copow d u3))) ->
    Vec r (Copow b (Copow c (Copow d u4))) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copow a (Copow b (Copow c (Copow d v))))
intersectFourDense x y z w f =
    intersect3 x y z $ \x' y' z' ->
    intersect3 x' y' w $ \x'' y'' w' ->
    intersect3 x'' z' w' $ \x''' z'' w'' ->
    intersect3 y'' z'' w'' $ \y''' z''' w''' ->
    f x''' y''' z''' w'''

traditionalIntersectFourDense :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d) => 
    Vec r (Copow a (Copow b (Copow c u1))) ->
    Vec r (Copow a (Copow b (Copow d u2))) ->
    Vec r (Copow a (Copow c (Copow d u3))) ->
    Vec r (Copow b (Copow c (Copow d u4))) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copow a (Copow b (Copow c (Copow d v))))
traditionalIntersectFourDense x y z w f =
    let xy = intersect2 x y $ \x' y' -> intersect2 x' y' $ \x'' y'' -> materialiseProduct x'' y'' in
    intersect2 xy z $ \xy' z' ->
    let xyz' = hmapCopow (\xy'' -> intersect2 xy'' z' $ \xy''' z'' -> intersect2 xy''' z'' (.*.)) xy' in
    intersect2 xyz' w $ \xyz'' w' ->
    intersect2 xyz'' w' $ \xyz''' w'' ->
    intersect2 xyz''' w'' $ \xyz'''' w''' ->
    tensorExt (\xy'''' z'''' -> tensorExt (\x'''' y'''' -> f x'''' y'''' z'''' w''') xy'''') xyz''''

intersectFourTriangles :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d, FirstOrder e, FirstOrder f) =>
    Vec r (Copow a (Copow d u1)) ->
    Vec r (Copow a (Copow e u2)) ->
    Vec r (Copow d (Copow e u3)) ->
    Vec r (Copow b (Copow d u4)) ->
    Vec r (Copow b (Copow f u5)) ->
    Vec r (Copow d (Copow f u6)) ->
    Vec r (Copow c (Copow e u7)) ->
    Vec r (Copow c (Copow f u8)) ->
    Vec r (Copow e (Copow f u9)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r u5  -> Vec r u6 -> Vec r u7 -> Vec r u8 -> Vec r u9 -> Vec r v) ->
    Vec r (Copow a (Copow b (Copow c (Copow d (Copow e (Copow f v))))))
intersectFourTriangles x1 x2 x3 x4 x5 x6 x7 x8 x9 f =
    intersect2 x1 x2 $ \x1' x2' ->
    intersect2 x4 x5 $ \x4' x5' ->
    intersect2 x7 x8 $ \x7' x8' ->
    intersect4 x1' x3 x4' x6 $ \x1'' x3' x4'' x6' ->
    intersect4 x2' x3' x7' x9 $ \x2'' x3'' x7'' x9' ->
    intersect4 x5' x6' x8' x9' $ \x5'' x6'' x8'' x9'' ->
    f x1'' x2'' x3'' x4'' x5'' x6'' x7'' x8'' x9''

traditionalIntersectFourTriangles :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d, FirstOrder e, FirstOrder f) =>
    Vec r (Copow a (Copow d u1)) ->
    Vec r (Copow a (Copow e u2)) ->
    Vec r (Copow d (Copow e u3)) ->
    Vec r (Copow b (Copow d u4)) ->
    Vec r (Copow b (Copow f u5)) ->
    Vec r (Copow d (Copow f u6)) ->
    Vec r (Copow c (Copow e u7)) ->
    Vec r (Copow c (Copow f u8)) ->
    Vec r (Copow e (Copow f u9)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r u5  -> Vec r u6 -> Vec r u7 -> Vec r u8 -> Vec r u9 -> Vec r v) ->
    Vec r (Copow a (Copow b (Copow c (Copow d (Copow e (Copow f v))))))
traditionalIntersectFourTriangles x1 x2 x3 x4 x5 x6 x7 x8 x9 f =
    let x123 = traditionalIntersectThreeCycle x1 x2 x3 (\x1' x2' x3' -> x1' .*. x2' .*. x3') in
    let x456 = traditionalIntersectThreeCycle x4 x5 x6 (\x4' x5' x6' -> x4' .*. x5' .*. x6') in
    let x789 = traditionalIntersectThreeCycle x7 x8 x9 (\x7' x8' x9' -> x7' .*. x8' .*. x9') in
    each x123 $ \x123' -> each x456 $ \x456' -> each x789 $ \x789' ->
    traditionalIntersectThreeCycle x123' x456' x789' $ \x123'' x456'' x789'' ->
    extTensor3 x123'' $ \x1'' x2'' x3'' ->
    extTensor3 x456'' $ \x4'' x5'' x6'' ->
    extTensor3 x789'' $ \x7'' x8'' x9'' ->
    f x1'' x2'' x3'' x4'' x5'' x6'' x7'' x8'' x9''

each :: (Ring r, FirstOrder a) => Vec r (Copow a u) -> (Vec r u -> Vec r v) -> Vec r (Copow a v)
each = flip hmapCopow

materialiseProduct :: (Ring r, FirstOrder a, FirstOrder b) =>
    Vec r (Copow a u) -> Vec r (Copow b v) -> Vec r (Copow a (Copow b (u :*: v)))
materialiseProduct x y = hmapCopow (\x' -> tick $ hmapCopow (\y' -> tick $ x' .*. y') y) x
