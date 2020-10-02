{-# LANGUAGE GADTs, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances, TypeFamilies, TypeOperators, DataKinds, KindSignatures #-}
module ModuleTheory.Intersect (
        -- Join(..),
        -- JoinMany(..),
        intersect2,
        intersect3,
        intersectThreeCycle,
        traditionalIntersectThreeCycle,
        intersectFourCycle,
        intersectFourCycle',
        traditionalIntersectFourCycle,
        intersectFourDense,
        traditionalIntersectFourDense,
        intersectFourTriangles,
        traditionalIntersectFourTriangles,
    ) where

import Debug.Trace

import ModuleTheory.Space
import ModuleTheory.Vector
import ModuleTheory.Tick

intersect2 :: (Ring r, FirstOrder a) => Vec r (Copi a u1) -> Vec r (Copi a u2) -> (Vec r u1 -> Vec r u2 -> Vec r v) -> Vec r (Copi a v)
intersect2 u1 u2 f = tick $ intersect (\_ x y -> tick $ f x y) u1 u2

intersect2' :: (Ring r, FirstOrder a) => Vec r (Copi a u1) -> Vec r (Copi a u2) -> (a -> Vec r u1 -> Vec r u2 -> Vec r v) -> Vec r (Copi a v)
intersect2' u1 u2 f = tick $ intersect (\a x y -> tick $ f a x y) u1 u2

intersect3 :: (Ring r, FirstOrder a) =>
    Vec r (Copi a u1) -> Vec r (Copi a u2) -> Vec r (Copi a u3) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r v) ->
    Vec r (Copi a v)
intersect3 u1 u2 u3 f = intersect2 u1 (intersect2 u2 u3 (.*.)) $ \x1 -> tensorExt $ \x2 x3 -> f x1 x2 x3

intersect4 :: (Ring r, FirstOrder a) =>
    Vec r (Copi a u1) -> Vec r (Copi a u2) -> Vec r (Copi a u3) -> Vec r (Copi a u4) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copi a v)
intersect4 u1 u2 u3 u4 f = intersect2 u1 (intersect3 u2 u3 u4 tensor3) $ \x1 -> tensorExt $ \x2 -> tensorExt $ \x3 x4 -> f x1 x2 x3 x4

intersectThreeCycle :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c) => 
    Vec r (Copi a (Copi b u1)) ->
    Vec r (Copi a (Copi c u2)) ->
    Vec r (Copi b (Copi c u3)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r v) ->
    Vec r (Copi a (Copi b (Copi c v)))
intersectThreeCycle x y z f =
    intersect2 x y $ \x' y' ->
    intersect2 x' z $ \x'' z' ->
    intersect2 y' z' $ \y'' z'' ->
    f x'' y'' z''

traditionalIntersectThreeCycle :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c) => 
    Vec r (Copi a (Copi b u1)) ->
    Vec r (Copi a (Copi c u2)) ->
    Vec r (Copi b (Copi c u3)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r v) ->
    Vec r (Copi a (Copi b (Copi c v)))
traditionalIntersectThreeCycle x y z f =
    intersect2 x y $ \x' y' ->
    let w = materialiseProduct x' y' in
    intersect2 w z $ \w' z' ->
    intersect2 w' z' $ \w'' z'' ->
    tensorExt (\x'' y'' -> f x'' y'' z'') w''

intersectFourCycle :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d) => 
    Vec r (Copi a (Copi b u1)) ->
    Vec r (Copi b (Copi c u2)) ->
    Vec r (Copi c (Copi d u3)) ->
    Vec r (Copi a (Copi d u4)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copi a (Copi b (Copi c (Copi d v))))
intersectFourCycle x y z w f =
    intersect2 x w $ \x' w' ->
    intersect2 x' y $ \x'' y' ->
    intersect2 y' z $ \y'' z' ->
    intersect2 z' w' $ \z'' w'' ->
    f x'' y'' z'' w''

intersectFourCycle' :: (Ring r, Show a, Show b, Show c, Show d, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d) => 
    Vec r (Copi a (Copi b u1)) ->
    Vec r (Copi b (Copi c u2)) ->
    Vec r (Copi c (Copi d u3)) ->
    Vec r (Copi a (Copi d u4)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copi a (Copi b (Copi c (Copi d v))))
intersectFourCycle' x y z w f =
    traceShow () $
    intersect2' x w $ \a x' w' ->
    traceShow a $
    intersect2' x' y $ \b x'' y' ->
    traceShow (a, b) $
    intersect2' y' z $ \c y'' z' ->
    traceShow (a, b, c) $
    intersect2' z' w' $ \d z'' w'' ->
    traceShow (a, b, c, d) $
    f x'' y'' z'' w''

traditionalIntersectFourCycle :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d) => 
    Vec r (Copi a (Copi b u1)) ->
    Vec r (Copi b (Copi c u2)) ->
    Vec r (Copi c (Copi d u3)) ->
    Vec r (Copi a (Copi d u4)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copi a (Copi b (Copi c (Copi d v))))
traditionalIntersectFourCycle x y z w f =
    intersect2 x w $ \x' w' ->
    let p = materialiseProduct x' w' in
    traditionalIntersectThreeCycle y p z $ \y'' p'' z'' ->
    tensorExt (\x'' w'' -> f x'' y'' z'' w'') p''

intersectFourDense :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d) => 
    Vec r (Copi a (Copi b (Copi c u1))) ->
    Vec r (Copi a (Copi b (Copi d u2))) ->
    Vec r (Copi a (Copi c (Copi d u3))) ->
    Vec r (Copi b (Copi c (Copi d u4))) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copi a (Copi b (Copi c (Copi d v))))
intersectFourDense x y z w f =
    intersect3 x y z $ \x' y' z' ->
    intersect3 x' y' w $ \x'' y'' w' ->
    intersect3 x'' z' w' $ \x''' z'' w'' ->
    intersect3 y'' z'' w'' $ \y''' z''' w''' ->
    f x''' y''' z''' w'''

traditionalIntersectFourDense :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d) => 
    Vec r (Copi a (Copi b (Copi c u1))) ->
    Vec r (Copi a (Copi b (Copi d u2))) ->
    Vec r (Copi a (Copi c (Copi d u3))) ->
    Vec r (Copi b (Copi c (Copi d u4))) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r v) ->
    Vec r (Copi a (Copi b (Copi c (Copi d v))))
traditionalIntersectFourDense x y z w f =
    let xy = intersect2 x y $ \x' y' -> intersect2 x' y' $ \x'' y'' -> materialiseProduct x'' y'' in
    intersect2 xy z $ \xy' z' ->
    let xyz' = hmapCopi (\xy'' -> intersect2 xy'' z' $ \xy''' z'' -> intersect2 xy''' z'' (.*.)) xy' in
    intersect2 xyz' w $ \xyz'' w' ->
    intersect2 xyz'' w' $ \xyz''' w'' ->
    intersect2 xyz''' w'' $ \xyz'''' w''' ->
    tensorExt (\xy'''' z'''' -> tensorExt (\x'''' y'''' -> f x'''' y'''' z'''' w''') xy'''') xyz''''

intersectFourTriangles :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d, FirstOrder e, FirstOrder f) =>
    Vec r (Copi a (Copi d u1)) ->
    Vec r (Copi a (Copi e u2)) ->
    Vec r (Copi d (Copi e u3)) ->
    Vec r (Copi b (Copi d u4)) ->
    Vec r (Copi b (Copi f u5)) ->
    Vec r (Copi d (Copi f u6)) ->
    Vec r (Copi c (Copi e u7)) ->
    Vec r (Copi c (Copi f u8)) ->
    Vec r (Copi e (Copi f u9)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r u5  -> Vec r u6 -> Vec r u7 -> Vec r u8 -> Vec r u9 -> Vec r v) ->
    Vec r (Copi a (Copi b (Copi c (Copi d (Copi e (Copi f v))))))
intersectFourTriangles x1 x2 x3 x4 x5 x6 x7 x8 x9 f =
    intersect2 x1 x2 $ \x1' x2' ->
    intersect2 x4 x5 $ \x4' x5' ->
    intersect2 x7 x8 $ \x7' x8' ->
    intersect4 x1' x3 x4' x6 $ \x1'' x3' x4'' x6' ->
    intersect4 x2' x3' x7' x9 $ \x2'' x3'' x7'' x9' ->
    intersect4 x5' x6' x8' x9' $ \x5'' x6'' x8'' x9'' ->
    f x1'' x2'' x3'' x4'' x5'' x6'' x7'' x8'' x9''

traditionalIntersectFourTriangles :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d, FirstOrder e, FirstOrder f) =>
    Vec r (Copi a (Copi d u1)) ->
    Vec r (Copi a (Copi e u2)) ->
    Vec r (Copi d (Copi e u3)) ->
    Vec r (Copi b (Copi d u4)) ->
    Vec r (Copi b (Copi f u5)) ->
    Vec r (Copi d (Copi f u6)) ->
    Vec r (Copi c (Copi e u7)) ->
    Vec r (Copi c (Copi f u8)) ->
    Vec r (Copi e (Copi f u9)) ->
    (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r u4 -> Vec r u5  -> Vec r u6 -> Vec r u7 -> Vec r u8 -> Vec r u9 -> Vec r v) ->
    Vec r (Copi a (Copi b (Copi c (Copi d (Copi e (Copi f v))))))
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

each :: (Ring r, FirstOrder a) => Vec r (Copi a u) -> (Vec r u -> Vec r v) -> Vec r (Copi a v)
each = flip hmapCopi

materialiseProduct :: (Ring r, FirstOrder a, FirstOrder b) =>
    Vec r (Copi a u) -> Vec r (Copi b v) -> Vec r (Copi a (Copi b (u :*: v)))
materialiseProduct x y = hmapCopi (\x' -> tick $ hmapCopi (\y' -> tick $ x' .*. y') y) x

