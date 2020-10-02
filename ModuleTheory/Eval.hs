{-# LANGUAGE GADTs, TypeOperators, DataKinds #-}
module ModuleTheory.Eval (
        ev,
{-
        evcBase,
        kleisli,
        evc,
        evh,
        measure,
-}
    ) where

import Prelude hiding (sum)
import Data.Maybe
import Data.Char
import qualified Data.List as L
import qualified Data.IntMap as M

import ModuleTheory.Space
import ModuleTheory.Vector
--import ModuleTheory.Base

ev :: (Ring r) => Vec r (u :-> v) -> Vec r u -> Vec r v
ev Zero _ = zero
ev _ Zero = zero
ev (Add f g) x = f `ev` x .+. g `ev` x
ev (Mul r f) x = r *. f `ev` x
ev (Gen f) x = evGen f x

infixl 9 `ev`

evGen :: (Ring r) => Gen r (u :-> v) -> Vec r u -> Vec r v
evGen _ Zero = zero
evGen (PiH f) x = undefined
evGen (CopiH f) x = evPi f x
evGen IdH x = x
evGen (ComposeH f g) x = f `ev` (g `ev` x)
evGen (AppH f x) y = f `ev` (x .*. y)
evGen CurryCopiH x = curryCopiProd x
evGen f (Add x y) = f `evGen` x .+. f `evGen` y
evGen f (Mul r x) = r *. f `evGen` x
evGen f (Gen x) = evGenGen f x

evGenGen :: (Ring r) => Gen r (u :-> v) -> Gen r u -> Vec r v
evGenGen AddH (DirectSum x y) = x .+. y
evGenGen AddManyH x = collectGen x
evGenGen MulH (Tensor r y) = getScalar r *. y
evGenGen (ParH f g) (DirectSum x y) = Gen $ DirectSum (f `ev` x) (g `ev` y)
evGenGen (KroneckerH f g) (Tensor x y) = f `ev` x .*. g `ev` y
evGenGen SwapH (Tensor x y) = Gen $ Tensor y x
evGenGen FanoutH (Tensor x y) = intersect (const (.*.)) x y
--evGenGen FanoutPiCopiH (Tensor f x) = mapCopi (\b y -> evPi f (inj b (mkScalar 1)) .*. y) x
--evGenGen FreeTensorH (Tensor x y) = Gen $ CopiTensor x y
evGenGen FreeTensorInvH (CopiProd x) = sum [inj b r .*. inj c one | (b, y) <- decomposeCoprod x, (c, r) <- decomposeCoprod y]
--evGenGen FreeTensorInvH (CopiTensor x y) = Gen $ Tensor x y
evGenGen ComposeHomCopiH (Tensor f x) = mapCopi (const $ ev f) x

evPi :: (Ring r, FirstOrder b) => Vec r (Pi b (u :-> v)) -> Vec r (Copi b u) -> Vec r v
evPi f x = linear (\f' -> evPiGen f' x) f

evPiGen :: (Ring r, FirstOrder b) => Gen r (Pi b (u :-> v)) -> Vec r (Copi b u) -> Vec r v
evPiGen (PiExt f) x = sum [f b `ev` y | (b, y) <- decomposeCoprod x]
-- evPiGen (PiMap f) x = sum [inj (f b `ev` y | (b, y) <- decomposeCoprod x]
{-
evMap :: CHom b c -> b -> Maybe c
evMap (IntMap b c) b' = if b == b' then Just c else Nothing
evMap (ProdMap m) (b1, b2) = evMap m b1 >>= \m' -> evMap m' b2
evMap (LeftMap m1) (Left b1) = evMap m1 b1
evMap (LeftMap m1) (Right _) = Nothing
evMap (RightMap m2) (Left _) = Nothing
evMap (RightMap m2) (Right b2) = evMap m2 b2

evcBase :: (Ring k) => Vec k (CHom b c) -> b -> Vec k c
evcBase ZeroV _ = zero
evcBase (AddV f g) b = f `evcBase` b .+. g `evcBase` b
evcBase (MulV k f) b = k *. f `evcBase` b
evcBase (InjV map) b = maybe zero inj (evMap map b)
evcBase (ComposeC f g) b = f `evc` (g `evcBase` b)
evcBase (SingleC b x) b' = if b == b' then x else zero
evcBase (ScalarC x) K = x
evcBase (IntC m) b = M.findWithDefault zero b m
evcBase (CharC m) b = M.findWithDefault zero (ord b) m
evcBase (ProdC f) (b1, b2) = f `evcBase` b1 `evcBase` b2
evcBase (SumC f1 f2) (Left b1) = f1 `evcBase` b1
evcBase (SumC f1 f2) (Right b2) = f2 `evcBase` b2
evcBase (PolyC f) [] = f `evcBase` Left K
evcBase (PolyC f) (b : bs) = f `evcBase` Right (b, bs)
-- evcBase (VecC f) x = f `evcBase` toWeightedBaseList x

{-
evhBase :: (Ring k) => Vec k (Hom b c) -> b -> Vec k c
evhBase ZeroV b = zero
evhBase (AddV f g) b = f `evhBase` b .+. g `evhBase` b
evhBase (MulV k f) b = k *. f `evhBase` b
evhBase (InjV f) b = case f of {}
evhBase (BaseH f) b = f b
evhBase (BaseToBaseH f) b = inj $ f b
evhBase IdH b = inj b
evhBase (ComposeH f g) b = f `evh` (g `evhBase` b)
evhBase (ConstH x) b = x
evhBase AddH (Left b) = inj b
evhBase AddH (Right b) = inj b
evhBase PolyMulH (b, c) = PolyMulV (inj b .*. inj c)
evhBase (ParH f g) (Left b) = SumV (f `evhBase` b) zero
evhBase (ParH f g) (Right b) = SumV zero (g `evhBase` b)
evhBase (KroneckerH f g) (b, c) = f `evhBase` b .*. g `evhBase` c
evhBase DupH b = SumV (inj b) (inj b)
evhBase ZipH b = inj (b, b)
evhBase SingletonH b = inj [b]
evhBase UnconsH [] = SumV one zero
evhBase UnconsH (b : bs) = SumV zero (inj b .*. inj bs)
evhBase TensorFstIdH (K, c) = inj c
evhBase TensorSndIdH (b, K) = inj b
evhBase TensorRevFstIdH c = one .*. inj c
evhBase TensorRevSndIdH b = inj b .*. one
evhBase TensorAssocH ((b, c), d) = inj (b, (c, d))
evhBase TensorRevAssocH (b, (c, d)) = inj ((b, c), d)
evhBase (MapH f) (IntMap b c) = IntC (M.singleton b (f `evhBase` c))
evhBase (MapH f) (CharMap b c) = CharC (M.singleton (ord b) (f `evhBase` c))
evhBase (MapH f) (ProdMap m) = ProdC $ MapH (MapH f) `evhBase` m
evhBase (MapH f) (LeftMap m) = SumC (MapH f `evhBase` m) zero
evhBase (MapH f) (RightMap m) = SumC zero (MapH f `evhBase` m)
evhBase MkIntH (b, c) = inj $ IntMap b c
evhBase MkCharH (b, c) = inj $ CharMap b c
evhBase AssocsH (ScalarMap b) = one .*. inj b
evhBase AssocsH (IntMap b c) = inj b .*. inj c
evhBase AssocsH (CharMap b c) = inj b .*. inj c
evhBase AssocsH (ProdMap m) = (TensorRevAssocH # IdH .&. AssocsH) `evh` (AssocsH `evhBase` m)
evhBase AssocsH (LeftMap m) = (inLeftH .&. IdH # AssocsH) `evhBase` m
evhBase AssocsH (RightMap m) = (inRightH .&. IdH # AssocsH) `evhBase` m
evhBase AssocsH (PolyMap m) = ((AddH # ConstH (inj []) .|. (PolyMulH # SingletonH .&. IdH)) .&. IdH # AssocsH) `evhBase` m
evhBase AssocsH (VecMap m) = (BaseH (inj . fromWeightedBaseList) .&. IdH # AssocsH) `evhBase` m
evhBase !f !b = undefined
-}

kleisli :: (Ring r, Base b) => (b -> Vec r c) -> Vec r b -> Vec r c
kleisli f x = baseFold x (\b r r -> r *. f b .+. r) 1 zero

evc :: (Ring r) => Vec r (CHom b c) -> Vec r b -> Vec r c
evc ZeroV x = zero
evc (AddV f g) x = f `evc` x .+. g `evc` x
evc (MulV r f) x = r *. f `evc` x
-- evc f x = baseFold x (\b k r -> f `evcBase` b .+. r) 1 zero

infixl 9 `evc`

evh :: (Ring r) => Vec r (Hom b c) -> Vec r b -> Vec r c
evh ZeroV x = zero
evh f ZeroV = zero
evh (AddV f g) x = f `evh` x .+. g `evh` x
evh (MulV r f) x = r *. f `evh` x
evh (BaseH f) x = kleisli f x
evh (BaseToBaseH f) x = kleisli (inj . f) x
evh IdH x = x
evh (ComposeH f g) x = f `evh` (g `evh` x)
evh (ConstH x) y = measure y *. x
evh AddH (InjV (Left b)) = inj b
evh AddH (InjV (Right b)) = inj b
evh AddH (SumV x y) = x .+. y
evh PolyMulH x = PolyMulV x
evh (ParH f g) (InjV (Left b)) = SumV (f `evh` inj b) zero
evh (ParH f g) (InjV (Right b)) = SumV zero (g `evh` inj b)
evh (ParH f g) (SumV x y) = SumV (f `evh` x) (g `evh` y)
evh (KroneckerH f g) (InjV (b, c)) = f `evh` inj b .*. g `evh` inj c
evh (KroneckerH f g) (TensorV x y) = f `evh` x .*. g `evh` y
evh DiagH x = SumV x x
evh (IntersectH f g) x = f `evh` x .*. g `evh` x
evh SingletonH x = PolySingleV x
evh UnconsH (InjV []) = SumV one zero
evh UnconsH (InjV (b : bs)) = SumV zero (inj b .*. inj bs)
evh UnconsH (PolySingleV x) = SumV zero (x .*. inj [])
evh TensorFstIdH (TensorV x y) = measure x *. y
evh TensorSndIdH (TensorV x y) = x .* measure y
evh TensorRevFstIdH x = one .*. x
evh TensorRevSndIdH x = x .*. one
evh TensorAssocH (TensorV x y) = sum [x1 .*. (x2 .*. y) | (x1, x2) <- decomposeTensor x]
evh TensorRevAssocH (TensorV x y) = sum [(x .*. y1) .*. y2 | (y1, y2) <- decomposeTensor y]
evh (MapH f) (SingleC b x) = SingleC b (f `evh` x)
evh (MapH f) (ScalarC x) = ScalarC (f `evh` x)
evh (MapH f) (IntC m) = IntC $ M.map (evh f) m
evh (MapH f) (CharC m) = CharC $ M.map (evh f) m
evh (MapH f) (ProdC g) = ProdC $ MapH (MapH f) `evh` g
evh (MapH f) (SumC g h) = SumC (MapH f `evh` g) (MapH f `evh` h)
evh (MapH f) (PolyC g) = PolyC $ MapH f `evh` g
evh (MapH f) (VecC g) = VecC $ MapH f `evh` g
evh IntersectCHomH (TensorV g h) = intersectCHom g h
evh IntersectHomCHomH (TensorV g h) = intersectHomCHom g h
evh IntersectHomH (TensorV g h) = IntersectH g h
evh MkCHomH (InjV (b, c)) = SingleC b (inj c)
evh MkCHomH (TensorV (InjV b) x) = SingleC b x
evh MkCHomH x = mkCompactH `evh` x
evh MkScalarH x = ScalarC x
evh MkIntH x = IntC $ M.fromListWith (.+.) [(b, r *. z) | (y, z) <- decomposeTensor x, (b, r) <- toWeightedBaseList y]
evh MkCharH x = CharC $ M.fromListWith (.+.) [(ord b, r *. z) | (y, z) <- decomposeTensor x, (b, r) <- toWeightedBaseList y]
evh UncurryH f = ProdC f
evh MkSumH f = uncurry SumC (decomposeSum f)
evh MkPolyH f = PolyC f
evh MkVecH f = VecC f
evh AssocsH (SingleC b x) = inj b .*. x
evh AssocsH (ScalarC x) = one .*. x
evh AssocsH (IntC m) = sum [inj b .*. x | (b, x) <- M.toList m]
evh AssocsH (CharC m) = sum [inj (chr b) .*. x | (b, x) <- M.toList m]
evh AssocsH (ProdC f) = (TensorRevAssocH # IdH .&. AssocsH # AssocsH) `evh` f
evh AssocsH (SumC f g) = tensorRevDistH `evh` SumV (AssocsH `evh` f) (AssocsH `evh` g)
evh AssocsH (PolyC f) = ((AddH # ConstH (inj []) .|. (PolyMulH # SingletonH .&. IdH)) .&. IdH # AssocsH) `evh` f
evh AssocsH (VecC f) = (BaseToBaseH fromWeightedBaseList .&. IdH # AssocsH) `evh` f
evh f (AddV x y) = f `evh` x .+. f `evh` y
evh f (MulV r x) = r *. f `evh` x
evh f x | dump (f .*. x) = undefined

infixl 9 `evh`

intersectCHom :: (Ring r) => Vec r (CHom b c) -> Vec r (CHom b d) -> Vec r (CHom b (c, d))
intersectCHom (SingleC b x) g = SingleC b (x .*. g `evcBase` b)
intersectCHom f (SingleC b y) = SingleC b (f `evcBase` b .*. y)
intersectCHom (ScalarC x) (ScalarC y) = ScalarC (x .*. y)
intersectCHom (IntC m1) (IntC m2) = IntC $ M.intersectionWith (.*.) m1 m2
intersectCHom (CharC m1) (CharC m2) = CharC $ M.intersectionWith (.*.) m1 m2
intersectCHom (ProdC f) (ProdC g) = ProdC $ MapH IntersectCHomH `evh` intersectCHom f g
intersectCHom (SumC f1 f2) (SumC g1 g2) = SumC (intersectCHom f1 g1) (intersectCHom f2 g2)
intersectCHom (PolyC f) (PolyC g) = PolyC $ intersectCHom f g
intersectCHom (VecC f) (VecC g) = VecC $ intersectCHom f g

intersectHomCHom :: (Ring r) => Vec r (Hom b c) -> Vec r (CHom b d) -> Vec r (CHom b (c, d))
intersectHomCHom f (ScalarC x) = ScalarC (f `evh` inj K .*. x)
intersectHomCHom f (IntC m) = IntC $ M.mapWithKey (\b x -> f `evh` inj b .*. x) m
intersectHomCHom f (CharC m) = CharC $ M.mapWithKey (\b x -> f `evh` inj (chr b) .*. x) m
intersectHomCHom f (ProdC g) = ProdC $ MapH IntersectHomCHomH `evh` intersectHomCHom (CurryH f) g
intersectHomCHom f (SumC g h) = SumC (intersectHomCHom (f # inLeftH) g) (intersectHomCHom (f # inRightH) h)
intersectHomCHom f (PolyC g) = PolyC $ intersectHomCHom (f # ConsH) g

decomposeTensor :: (Ring r) => Vec r (b, c) -> [(Vec r b, Vec r c)]
decomposeTensor x = decomposeTensor' x 1 []

decomposeTensor' :: (Ring r) => Vec r (b, c) -> r -> [(Vec r b, Vec r c)] -> [(Vec r b, Vec r c)]
decomposeTensor' ZeroV !r = id
decomposeTensor' (AddV x y) !r = decomposeTensor' x r . decomposeTensor' y r
decomposeTensor' (MulV r' x) !r = decomposeTensor' x (r * r')
decomposeTensor' (InjV (b, c)) !r = (:) (r *. inj b, inj c)
decomposeTensor' (TensorV x y) !r = (:) (r *. x, y)

decomposeSum :: (Ring r) => Vec r (Either b c) -> (Vec r b, Vec r c)
decomposeSum ZeroV = (zero, zero)
decomposeSum (AddV x y) =
    let (xl, xr) = decomposeSum x in
    let (yl, yr) = decomposeSum y in
    (xl .+. yl, xr .+. yr)
decomposeSum (MulV r x) =
    let (xl, xr) = decomposeSum x in
    (r *. xl, r *. xr)
decomposeSum (InjV (Left b)) = (inj b, zero)
decomposeSum (InjV (Right c)) = (zero, inj c)
decomposeSum (SumV x y) = (x, y)

decomposeCSum :: (Ring r) => Vec r (CHom (Either b c) d) -> (Vec r (CHom b d), Vec r (CHom c d))
decomposeCSum ZeroV = (zero, zero)
decomposeCSum (AddV x y) =
    let (xl, xr) = decomposeCSum x in
    let (yl, yr) = decomposeCSum y in
    (xl .+. yl, xr .+. yr)
decomposeCSum (MulV r x) =
    let (xl, xr) = decomposeCSum x in
    (r *. xl, r *. xr)
decomposeCSum (InjV (LeftMap b)) = (inj b, zero)
decomposeCSum (InjV (RightMap c)) = (zero, inj c)
decomposeCSum (SumC x y) = (x, y)
-}
