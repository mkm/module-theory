{-# LANGUAGE GADTs, KindSignatures, ConstraintKinds, StandaloneDeriving, TypeOperators, DataKinds, TypeFamilies, FlexibleInstances, FlexibleContexts #-}
module ModuleTheory.Vector (
        Ring,
        Vec(..),
        Gen(..),
        zero,
        (.+.),
        (.-.),
        (*.),
        (.*),
        (.*.),
        tensor3,
        mkScalar,
        getScalar,
        sumList,
        linear,
        bilinear,
        decomposeSum,
        decomposeTensor,
        tensorExt,
        extTensor,
        extTensor3,
        mapTensor,
        powExt,
        appPow,
        mapCopow,
        hmapCopow,
        copowExt,
        sum,
        weight,
        freeExt,
        mapFree,
        collect,
        collect2,
        collect3,
        collect4,
        collect5,
        collect6,
        Based(..),
        FirstOrder(..),
        cinj,
        csingle,
        ccopowExt,
        cfreeExt,
        ShowVec(..),
        curryCopowProd,
    ) where

import Prelude hiding (sum)
import Data.Kind
import Data.Char
import qualified Data.List as L
import Data.IntMap (IntMap)
import qualified Data.IntMap as M
import Control.DeepSeq
import Control.Arrow
import System.IO.Unsafe

import ModuleTheory.Space

type Ring r = (Eq r, Num r)

data Vec r v = Zero | Add (Vec r v) (Vec r v) | Mul r (Vec r v) | Gen (Gen r v)

data family Gen r (v :: Space) :: Type

data instance Gen r R = One

newtype instance Gen r (() :=> v) = CopowUnit { fromCopowUnit :: Vec r v }

newtype instance Gen r (Int :=> v) = CopowInt { fromCopowInt :: IntMap (Vec r v) }

newtype instance Gen r (Char :=> v) = CopowChar { fromCopowChar :: IntMap (Vec r v) }

data instance Gen r (Either b c :=> v) = CopowSum (Vec r (b :=> v)) (Vec r (c :=> v))

newtype instance Gen r ((b, c) :=> v) = CopowProd (Vec r (b :=> c :=> v))

data instance Gen r ([b] :=> v) = CopowPoly (Vec r v) (Vec r (b :=> [b] :=> v))

newtype instance Gen r (Vec s u :=> v) = CopowVec (Vec r ([(Basis u, s)] :=> v))

data instance Gen r (b :=>* v) = AdjoinUnit (Vec r v) (Vec r (b :=> v))

newtype instance Gen r (Pow b v) = PowExt { fromPow :: b -> Vec r v }

data instance Gen r (u :+: v) = DirectSum (Vec r u) (Vec r v)

data instance Gen r (u :*: v) = Tensor (Vec r u) (Vec r v)

data instance Gen r (Poly v) = ConstPoly (Vec r R) | InjPoly (Vec r v) | MulPoly (Vec r (Poly v)) (Vec r (Poly v))

newtype instance Gen r (u :-> v) = Hom (Vec r u -> Vec r v)

zero :: Vec r v
zero = Zero

(.+.) :: Vec r v -> Vec r v -> Vec r v
Zero .+. y = y
x .+. Zero = x
x .+. y = Add x y

infixl 7 .+.

(.-.) :: (Ring r) => Vec r v -> Vec r v -> Vec r v
x .-. y = x .+. (-1) *. y

infix 7 .-.

(*.) :: r -> Vec r v -> Vec r v
_ *. Zero = Zero
r *. x = Mul r x

infix 8 *.

(.*) :: Vec r v -> r -> Vec r v
Zero .* _ = Zero
x .* r = Mul r x

infix 8 .*

(.*.) :: Vec r u -> Vec r v -> Vec r (u :*: v)
Zero .*. _ = Zero
_ .*. Zero = Zero
x .*. y = Gen $ Tensor x y

infixr 8 .*.

tensor3 :: Vec r u -> Vec r v -> Vec r w -> Vec r (u :*: v :*: w)
tensor3 x y z = x .*. y .*. z

mkScalar :: (Ring r) => r -> Vec r R
mkScalar 0 = Zero
mkScalar 1 = Gen One
mkScalar r = Mul r (Gen One)

getScalar :: (Ring r) => Vec r R -> r
getScalar Zero = 0
getScalar (Add x y) = getScalar x + getScalar y
getScalar (Mul r x) = r * getScalar x
getScalar (Gen One) = 1

sumList :: [Vec r v] -> Vec r v
sumList = foldr (.+.) zero

linear :: (Gen r u -> Vec r v) -> Vec r u -> Vec r v
linear f Zero = zero
linear f (Add x y) = linear f x .+. linear f y
linear f (Mul r x) = r *. linear f x
linear f (Gen x) = f x

bilinear :: (Gen r u -> Gen r v -> Vec r w) -> Vec r u -> Vec r v -> Vec r w
bilinear f x y = linear (\x' -> linear (\y' -> f x' y') y) x

isNominallyZero :: Vec r v -> Bool
isNominallyZero Zero = True
isNominallyZero _ = False

zeroToNothing :: Vec r v -> Maybe (Vec r v)
zeroToNothing Zero = Nothing
zeroToNothing x = Just x

decomposeSum :: (Ring r) => Vec r (u :+: v) -> Gen r (u :+: v)
decomposeSum Zero = DirectSum zero zero
decomposeSum (Add x y) = DirectSum (x1 .+. y1) (x2 .+. y2)
    where
        DirectSum x1 x2 = decomposeSum x
        DirectSum y1 y2 = decomposeSum y
decomposeSum (Mul r x) = DirectSum (r *. x1) (r *. x2)
    where
        DirectSum x1 x2 = decomposeSum x
decomposeSum (Gen x) = x

decomposeTensor :: (Ring r) => Vec r (u :*: v) -> [Gen r (u :*: v)]
decomposeTensor x = decomposeTensor' x 1 []

decomposeTensor' :: (Ring r) => Vec r (u :*: v) -> r -> [Gen r (u :*: v)] -> [Gen r (u :*: v)]
decomposeTensor' Zero _ = id
decomposeTensor' (Add x y) r = decomposeTensor' x r . decomposeTensor' y r
decomposeTensor' (Mul r' x) r = decomposeTensor' x (r' * r)
decomposeTensor' (Gen (Tensor x y)) r = (:) $ Tensor (r *. x) y

tensorExt :: (Ring r) => (Vec r u -> Vec r v -> Vec r w) -> Vec r (u :*: v) -> Vec r w
tensorExt f Zero = Zero
tensorExt f (Add x y) = Add (tensorExt f x) (tensorExt f y)
tensorExt f (Mul r x) = Mul r (tensorExt f x)
tensorExt f (Gen (Tensor x y)) = f x y

extTensor :: (Ring r) => Vec r (u :*: v) -> (Vec r u -> Vec r v -> Vec r w) -> Vec r w
extTensor = flip tensorExt

extTensor3 :: (Ring r) => Vec r (u1 :*: u2 :*: u3) -> (Vec r u1 -> Vec r u2 -> Vec r u3 -> Vec r v) -> Vec r v
extTensor3 x f = extTensor x $ \x1 -> tensorExt $ \x2 x3 -> f x1 x2 x3

mapTensor :: (Ring r) => (Vec r u1 -> Vec r v1) -> (Vec r u2 -> Vec r v2) -> Vec r (u1 :*: u2) -> Vec r (v1 :*: v2)
mapTensor f g = tensorExt $ \u v -> f u .*. g v

powExt :: (a -> Vec r u) -> Vec r (Pow a u)
powExt = Gen . PowExt

appPow :: Vec r (Pow a u) -> a -> Vec r u
appPow Zero = const Zero
appPow (Add x y) = \a -> Add (appPow x a) (appPow y a)
appPow (Mul r x) = \a -> Mul r (appPow x a)
appPow (Gen x) = fromPow x

class (FirstOrder (Basis u)) => Based u where
    type Basis u :: Type
    single :: (Ring r) => Basis u -> Vec r u
    toList :: (Ring r) => Vec r u -> [(Basis u, r)]

fromList :: (Ring r, Based u) => [(Basis u, r)] -> Vec r u
fromList = sumList . map (\(b, r) -> r *. single b)

instance Based R where
    type Basis R = ()
    single () = Gen One
    toList Zero = []
    toList r = [((), getScalar r)]

instance (FirstOrder b) => Based (Free b) where
    type Basis (Free b) = b
    single x = inj x (Gen One)
    toList = map (\(b, r) -> (b, getScalar r)) . decomposeCopow

-- | A type is first-order if it can be used efficiently as the index of a copower. 
class Eq b => FirstOrder b where
    -- | Singleton mapping.
    inj :: b -> Vec r v -> Vec r (b :=> v)
    -- | Transform a copower generator by specifying what happens to 'inj b v'.
    mapCopowGen :: (Ring r) => (b -> Vec r u -> Vec r v) -> Gen r (b :=> u) -> Vec r (b :=> v)
    -- | Sum of the mappings contained in a copower generator.
    collectGen :: (Ring r) => Gen r (b :=> v) -> Vec r v
    -- | Intersection of two copowers.
    intersectCopow :: (Ring r) => (b -> Vec r u -> Vec r v -> Vec r w) -> Vec r (b :=> u) -> Vec r (b :=> v) -> Vec r (b :=> w)
    -- | Compute a list of mappings contained in a copower.
    decomposeCopow :: (Ring r) => Vec r (b :=> v) -> [(b, Vec r v)]

-- | Transform a copower by specifying what happens to 'inj b v'.
mapCopow :: (Ring r, FirstOrder b) => (b -> Vec r u -> Vec r v) -> Vec r (b :=> u) -> Vec r (b :=> v)
mapCopow = linear . mapCopowGen

-- | Transform a copower by specifying what happens to 'inj b v' independent of 'b'.
hmapCopow :: (Ring r, FirstOrder b) => (Vec r u -> Vec r v) -> Vec r (b :=> u) -> Vec r (b :=> v)
hmapCopow f = mapCopow (const f)

copowExt :: (Ring r, FirstOrder b) => (b -> Vec r u -> Vec r v) -> Vec r (b :=> u) -> Vec r v
copowExt f = sumList . map (uncurry f) . decomposeCopow

sum :: (Ring r, FirstOrder b) => Vec r (b :=> u) -> Vec r u
sum = copowExt (const id)

weight :: (Ring r, FirstOrder b) => Vec r (Free b) -> r
weight = getScalar . sum

freeExt :: (Ring r, FirstOrder b) => (b -> Vec r v) -> Vec r (Free b) -> Vec r v
freeExt f = copowExt (\b r -> getScalar r *. f b)

mapFree :: (Ring r, FirstOrder b, FirstOrder c) => (b -> c) -> Vec r (Free b) -> Vec r (Free c)
mapFree f = freeExt $ \b -> inj (f b) (Gen One)

-- | Sum of the mappings contained in a copower.
collect :: (Ring r, FirstOrder b)
    => Vec r (b :=> v) -> Vec r v
collect = linear collectGen

-- | Sum of the mappings contained in a nested copower.
collect2 :: (Ring r, FirstOrder a, FirstOrder b)
    => Vec r (a :=> b :=> v) -> Vec r v
collect2 = collect . collect

-- | Sum of the mappings contained in a nested copower.
collect3 :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c)
    => Vec r (a :=> b :=> c :=> v) -> Vec r v
collect3 = collect . collect . collect

-- | Sum of the mappings contained in a nested copower.
collect4 :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d)
    => Vec r (a :=> b :=> c :=> d :=> v) -> Vec r v
collect4 = collect . collect . collect . collect

-- | Sum of the mappings contained in a nested copower.
collect5 :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d, FirstOrder e) =>
    Vec r (a :=> b :=> c :=> d :=> e :=> v) -> Vec r v
collect5 = collect . collect . collect . collect . collect

-- | Sum of the mappings contained in a nested copower.
collect6 :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d, FirstOrder e, FirstOrder f) =>
    Vec r (a :=> b :=> c :=> d :=> e :=> f :=> v) -> Vec r v
collect6 = collect . collect . collect . collect . collect . collect

instance FirstOrder () where
    inj () x = Gen $ CopowUnit x
    mapCopowGen f (CopowUnit x) = Gen $ CopowUnit (f () x)
    collectGen (CopowUnit x) = x
    intersectCopow f x y = Gen . CopowUnit $ f () (linear fromCopowUnit x) (linear fromCopowUnit y)
    decomposeCopow x = [((), y) | let y = linear fromCopowUnit x, not (isNominallyZero y)]

canonicalCopowInt :: (Ring r) => r -> Vec r (Int :=> v) -> Gen r (Int :=> v)
canonicalCopowInt r Zero = CopowInt M.empty
canonicalCopowInt r (Add x y) = CopowInt $ M.unionWith (.+.) (fromCopowInt $ canonicalCopowInt r x) (fromCopowInt $ canonicalCopowInt r y)
canonicalCopowInt r (Mul r' x) = canonicalCopowInt (r * r') x
canonicalCopowInt 1 (Gen x) = x
canonicalCopowInt r (Gen x) = CopowInt $ M.map (r *.) (fromCopowInt x)

instance FirstOrder Int where
    inj b x = Gen . CopowInt $ M.singleton b x
    mapCopowGen f (CopowInt m) = Gen . CopowInt $ M.mapMaybeWithKey (\b -> zeroToNothing . f b) m
    collectGen (CopowInt m) = sumList $ M.elems m
    intersectCopow f x y = Gen . CopowInt $ M.intersectionWithKey f (fromCopowInt $ canonicalCopowInt 1 x) (fromCopowInt $ canonicalCopowInt 1 y)
    decomposeCopow = M.toList . fromCopowInt . canonicalCopowInt 1

canonicalCopowChar :: (Ring r) => r -> Vec r (Char :=> v) -> Gen r (Char :=> v)
canonicalCopowChar r Zero = CopowChar M.empty
canonicalCopowChar r (Add x y) = CopowChar $ M.unionWith (.+.) (fromCopowChar $ canonicalCopowChar r x) (fromCopowChar $ canonicalCopowChar r y)
canonicalCopowChar r (Mul r' x) = canonicalCopowChar (r * r') x
canonicalCopowChar 1 (Gen x) = x
canonicalCopowChar r (Gen x) = CopowChar $ M.map (r *.) (fromCopowChar x)

instance FirstOrder Char where
    inj b x = Gen . CopowChar $ M.singleton (ord b) x
    mapCopowGen f (CopowChar m) = Gen . CopowChar $ M.mapMaybeWithKey (\b -> zeroToNothing . f (chr b)) m
    collectGen (CopowChar m) = sumList $ M.elems m
    intersectCopow f x y = Gen . CopowChar $ M.intersectionWithKey (f . chr) (fromCopowChar $ canonicalCopowChar 1 x) (fromCopowChar $ canonicalCopowChar 1 y)
    decomposeCopow = map (chr *** id) . M.toList . fromCopowChar . canonicalCopowChar 1

partitionCopowSum :: Vec r (Either b c :=> v) -> (Vec r (b :=> v), Vec r (c :=> v))
partitionCopowSum Zero = (zero, zero)
partitionCopowSum (Add x y) = (xb .+. yb, xc .+. yc)
    where
        (xb, xc) = partitionCopowSum x
        (yb, yc) = partitionCopowSum y
partitionCopowSum (Mul r x) = (r *. xb, r *. xc)
    where
        (xb, xc) = partitionCopowSum x
partitionCopowSum (Gen (CopowSum xb xc)) = (xb, xc)

instance (FirstOrder b, FirstOrder c) => FirstOrder (Either b c) where
    inj (Left b) x = Gen $ CopowSum (inj b x) zero
    inj (Right c) x = Gen $ CopowSum zero (inj c x)
    mapCopowGen f (CopowSum x y) = Gen $ CopowSum (mapCopow (f . Left) x) (mapCopow (f . Right) y)
    collectGen (CopowSum x y) = collect x .+. collect y
    intersectCopow f x y = Gen $ CopowSum (intersectCopow (f . Left) xb yb) (intersectCopow (f . Right) xc yc)
        where
            (xb, xc) = partitionCopowSum x
            (yb, yc) = partitionCopowSum y
    decomposeCopow = uncurry (++) . (map (Left *** id) . decomposeCopow *** map (Right *** id) . decomposeCopow) . partitionCopowSum

curryCopowProd :: (Ring r) => Vec r ((b, c) :=> v) -> Vec r (b :=> c :=> v)
curryCopowProd = linear go
    where
        go :: (Ring r) => Gen r ((b, c) :=> v) -> Vec r (b :=> c :=> v)
        go (CopowProd x) = x

instance (FirstOrder b, FirstOrder c) => FirstOrder (b, c) where
    inj (b, c) x = Gen . CopowProd $ inj b (inj c x)
    mapCopowGen f x = Gen . CopowProd $ mapCopow (mapCopow . curry f) (curryCopowProd $ Gen x)
    collectGen (CopowProd x) = collect $ collect x
    intersectCopow f x y = Gen . CopowProd $ intersectCopow (intersectCopow . curry f) (curryCopowProd x) (curryCopowProd y)
    decomposeCopow x = [((b, c), z) | (b, y) <- decomposeCopow (curryCopowProd x), (c, z) <- decomposeCopow y]

partitionCopowList :: Vec r ([b] :=> v) -> (Vec r v, Vec r (b :=> [b] :=> v))
partitionCopowList Zero = (zero, zero)
partitionCopowList (Add x y) = (xNil .+. yNil, xCons .+. yCons)
    where
        (xNil, xCons) = partitionCopowList x
        (yNil, yCons) = partitionCopowList y
partitionCopowList (Mul r x) = (r *. xNil, r *. xCons)
    where
        (xNil, xCons) = partitionCopowList x
partitionCopowList (Gen (CopowPoly x xs)) = (x, xs)

instance (FirstOrder b) => FirstOrder [b] where
    inj [] x = Gen $ CopowPoly x zero
    inj (b : bs) x = Gen . CopowPoly zero $ inj b (inj bs x)
    mapCopowGen f (CopowPoly x xs) = Gen $ CopowPoly (f [] x) (mapCopow (\b -> mapCopow (f . (:) b)) xs)
    collectGen (CopowPoly x xs) = x .+. collect (collect xs)
    intersectCopow f x y = Gen $ CopowPoly (f [] xh yh) (intersectCopow (intersectCopow . (f .) . (:)) xt yt)
        where
            (xh, xt) = partitionCopowList x
            (yh, yt) = partitionCopowList y
    decomposeCopow x =
        [([], x0) | not (isNominallyZero x0)] ++
        [(b : bs, z) | (b, y) <- decomposeCopow xs, (bs, z) <- decomposeCopow y]
        where
            (x0, xs) = partitionCopowList x

instance (Ring r, Based u) => Eq (Vec r u) where
    u == v = toList u == toList v

canonicalCopowVec :: Vec r (Vec s u :=> v) -> Gen r (Vec s u :=> v)
canonicalCopowVec Zero = CopowVec Zero
canonicalCopowVec (Add x y) = CopowVec (x' .+. y')
    where
        CopowVec x' = canonicalCopowVec x
        CopowVec y' = canonicalCopowVec y
canonicalCopowVec (Mul r x) = CopowVec (r *. x')
    where
        CopowVec x' = canonicalCopowVec x
canonicalCopowVec (Gen x) = x

instance (Ring r, FirstOrder r, Based u) => FirstOrder (Vec r u) where
    inj u x = Gen . CopowVec $ inj (toList u) x
    mapCopowGen f (CopowVec x) = Gen . CopowVec $ mapCopow (f . fromList) x
    collectGen (CopowVec x) = collect x
    intersectCopow f x y = Gen . CopowVec $ intersectCopow (f . fromList) x' y'
        where
            CopowVec x' = canonicalCopowVec x
            CopowVec y' = canonicalCopowVec y
    decomposeCopow x = map (\(us, v) -> (fromList us, v)) (decomposeCopow x')
        where
            CopowVec x' = canonicalCopowVec x

cinj :: (FirstOrder b) => b -> Vec r v -> Vec r (b :=>* v)
cinj x v = Gen $ AdjoinUnit zero (inj x v)

csingle :: (FirstOrder b) => b -> Vec r (CFree b)
csingle b = cinj b (Gen One)

ccopowExt :: (Ring r, FirstOrder b) => (Vec r u -> Vec r v) -> (b -> Vec r u -> Vec r v) -> Vec r (b :=>* u) -> Vec r v
ccopowExt u f x = u xUnit .+. copowExt f xVal
    where
        AdjoinUnit xUnit xVal = decomposeCCopow x

cfreeExt :: (Ring r, FirstOrder b) => Vec r v -> (b -> Vec r v) -> Vec r (CFree b) -> Vec r v
cfreeExt u f = ccopowExt (\r -> getScalar r *. u) (\b r -> getScalar r *. f b)

decomposeCCopow :: Vec r (b :=>* v) -> Gen r (b :=>* v)
decomposeCCopow Zero = AdjoinUnit zero zero
decomposeCCopow (Add x y) = AdjoinUnit (xUnit .+. yUnit) (xVal .+. yVal)
    where
        AdjoinUnit xUnit xVal = decomposeCCopow x
        AdjoinUnit yUnit yVal = decomposeCCopow y
decomposeCCopow (Mul r x) = AdjoinUnit (r *. xUnit) (r *. xVal)
    where
        AdjoinUnit xUnit xVal = decomposeCCopow x
decomposeCCopow (Gen x) = x

class ShowVec (v :: Space) where
    showsVec :: (Show r, Ring r) => Vec r v -> ShowS
    showsVec = showsPrecVec 0
    showsPrecVec :: (Show r, Ring r) => Int -> Vec r v -> ShowS
    showsPrecVec _ = showsVec

instance (Show r, Ring r, ShowVec v) => Show (Vec r v) where
    showsPrec = showsPrecVec

instance ShowVec R where
    showsPrecVec d = showsPrec d . getScalar

instance (Show b, FirstOrder b, ShowVec v) => ShowVec (b :=> v) where
    showsPrecVec d =
        showSum s d . decomposeCopow
        where
            s d (b, x) = showParen (d > 10) $ showString "inj " . showsPrec 11 b . showString " " . showsPrec 11 x

instance (ShowVec v) => ShowVec (Pow b v) where
    showsPrecVec d x =
        showParen True $ showString "λ " . showsPrec 0 (appPow x undefined)

instance (ShowVec u, ShowVec v) => ShowVec (u :*: v) where
    showsPrecVec d = showSum s d . decomposeTensor
        where
            s d (Tensor x y) = showParen (d > 8) $ showsPrec 9 x . showString " .*. " . showsPrec 9 y

showSum :: (Int -> a -> ShowS) -> Int -> [a] -> ShowS
showSum _ _ [] = showString "zero"
showSum s d [x] = s d x
showSum s d xs = showParen (d > 7) $ foldr1 (.) (L.intersperse (showString " .+. ") (map (s 8) xs))

class NFVec (v :: Space) where
    rnfVec :: (Ring r, NFData r) => Gen r v -> ()

instance (Ring r, NFData r, NFVec v) => NFData (Gen r v) where
    rnf = rnfVec

instance (Ring r, NFData r, NFVec v) => NFData (Vec r v) where
    rnf Zero = ()
    rnf (Add x y) = rnf x `seq` rnf y
    rnf (Mul r x) = rnf r `seq` rnf x
    rnf (Gen x) = rnfVec x

instance NFVec R where
    rnfVec One = ()

instance (NFData a, FirstOrder a, NFVec v) => NFVec (a :=> v) where
    rnfVec = rnf . collectGen

instance (NFVec u, NFVec v) => NFVec (u :*: v) where
    rnfVec (Tensor x y) = rnf x `seq` rnf y
