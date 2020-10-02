{-# LANGUAGE GADTs, KindSignatures, ConstraintKinds, StandaloneDeriving, TypeOperators, DataKinds, TypeFamilies, FlexibleInstances, FlexibleContexts #-}
module ModuleTheory.Vector (
        Ring,
        Vec(..),
        Gen(..),
        zero,
        (.+.),
        (*.),
        (.*.),
        tensor3,
        mkScalar,
        one,
        getScalar,
        mul,
        mul3,
        scalarH,
        sumH,
        tensorH,
        idH,
        (#),
        appH,
        addH,
        addManyH,
        mulH,
        parH,
        kroneckerH,
        swapH,
        fanoutH,
        fanoutPiCopiH,
        --freeTensorH,
        --freeTensorInvH,
        composeHomCopiH,
        curryCopiH,
        sum,
        linear,
        bilinear,
        kronecker,
        tassocLtr,
        tassocRtl,
        decomposeSum,
        decomposeTensor,
        tensorExt,
        extTensor,
        extTensor3,
        appPi,
        mapCopi,
        hmapCopi,
        collect,
        collect2,
        collect3,
        collect4,
        collect5,
        collect6,
        FirstOrder(..),
        ShowVec(..),
        curryCopiProd,
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

newtype instance Gen r R = Scalar r

newtype instance Gen r (Copi () v) = CopiUnit { fromCopiUnit :: Vec r v }

newtype instance Gen r (Copi Int v) = CopiInt { fromCopiInt :: IntMap (Vec r v) }

newtype instance Gen r (Copi Char v) = CopiChar { fromCopiChar :: IntMap (Vec r v) }

data instance Gen r (Copi (Either b c) v) = CopiSum (Vec r (Copi b v)) (Vec r (Copi c v))

newtype instance Gen r (Copi (b, c) v) = CopiProd (Vec r (Copi b (Copi c v)))

data instance Gen r (Copi [b] v) = CopiPoly (Vec r v) (Vec r (Copi b (Copi [b] v)))

newtype instance Gen r (Pi b v) = PiExt { fromPi :: b -> Vec r v }

data instance Gen r (u :+: v) = DirectSum (Vec r u) (Vec r v)

data instance Gen r (u :*: v) = Tensor (Vec r u) (Vec r v)

data instance Gen r (Poly v) = ConstPoly (Vec r R) | InjPoly (Vec r v) | MulPoly (Vec r (Poly v)) (Vec r (Poly v))

data instance Gen r (u :-> v) where
    PiH :: Vec r (Copi b (u :-> v)) -> Gen r (Pi b u :-> v)
    CopiH :: (FirstOrder b) => Vec r (Pi b (u :-> v)) -> Gen r (Copi b u :-> v)
    ScalarH :: Vec r v -> Gen r (R :-> v)
    SumH :: Vec r (u :-> w) -> Vec r (v :-> w) -> Gen r (u :+: v :-> w)
    TensorH :: Vec r (u :-> v :-> w) -> Gen r (u :*: v :-> w)
    IdH :: Gen r (v :-> v)
    ComposeH :: Vec r (v :-> w) -> Vec r (u :-> v) -> Gen r (u :-> w)
    AppH :: Vec r (u :*: v :-> w) -> Vec r u -> Gen r (v :-> w)
    AddH :: Gen r (v :+: v :-> v)
    AddManyH :: (FirstOrder b) => Gen r (Copi b v :-> v)
    MulH :: Gen r (R :*: v :-> v)
    ParH :: Vec r (u1 :-> v1) -> Vec r (u2 :-> v2) -> Gen r (u1 :+: u2 :-> v1 :+: v2)
    KroneckerH :: Vec r (u1 :-> v1) -> Vec r (u2 :-> v2) -> Gen r (u1 :*: u2 :-> v1 :*: v2)
    SwapH :: Gen r (u :*: v :-> v :*: u)
    FanoutH :: (FirstOrder b) => Gen r (Copi b u :*: Copi b v :-> Copi b (u :*: v))
    FanoutPiCopiH :: (FirstOrder b) => Gen r (Pi b u :*: Copi b v :-> Copi b (u :*: v))
    FreeTensorH :: (FirstOrder b, FirstOrder c) => Gen r (Free b :*: Free c :-> Free (b, c))
    FreeTensorInvH :: (FirstOrder b, FirstOrder c) => Gen r (Free (b, c) :-> Free b :*: Free c)
    ComposeHomCopiH :: (FirstOrder b) => Gen r ((u :-> v) :*: Copi b u :-> Copi b v)
    CurryCopiH :: Gen r (Copi (b, c) v :-> Copi b (Copi c v))

zero :: Vec r v
zero = Zero

(.+.) :: Vec r v -> Vec r v -> Vec r v
Zero .+. y = y
x .+. Zero = x
x .+. y = Add x y

infixl 7 .+.

(*.) :: r -> Vec r v -> Vec r v
_ *. Zero = Zero
r *. x = Mul r x

infix 8 *.

(.*.) :: Vec r u -> Vec r v -> Vec r (u :*: v)
x .*. y = Gen $ Tensor x y

infixr 8 .*.

tensor3 :: Vec r u -> Vec r v -> Vec r w -> Vec r (u :*: v :*: w)
tensor3 x y z = x .*. y .*. z

mkScalar :: (Ring r) => r -> Vec r R
mkScalar 0 = Zero
mkScalar x = Gen (Scalar x)

one :: (Ring r) => Vec r R
one = mkScalar 1

getScalar :: (Ring r) => Vec r R -> r
getScalar Zero = 0
getScalar (Add x y) = getScalar x + getScalar y
getScalar (Mul r x) = r * getScalar x
getScalar (Gen (Scalar r)) = r

mul :: (Ring r) => Vec r (R :*: R) -> Vec r R
mul = tensorExt (*)

mul3 :: (Ring r) => Vec r (R :*: R :*: R) -> Vec r R
mul3 = tensorExt $ \x -> tensorExt $ \y z -> x * y * z

scalarH :: Vec r v -> Vec r (R :-> v)
scalarH x = Gen $ ScalarH x

sumH :: Vec r (u :-> w) -> Vec r (v :-> w) -> Vec r (u :+: v :-> w)
sumH f g = Gen $ SumH f g

tensorH :: Vec r (u :-> v :-> w) -> Vec r (u :*: v :-> w)
tensorH f = Gen $ TensorH f
    
idH :: Vec r (v :-> v)
idH = Gen IdH

(#) :: Vec r (v :-> w) -> Vec r (u :-> v) -> Vec r (u :-> w)
f # g = Gen $ ComposeH f g

appH :: Vec r (u :*: v :-> w) -> Vec r u -> Vec r (v :-> w)
appH f x = Gen $ AppH f x

addH :: Vec r (v :+: v :-> v)
addH = Gen AddH

addManyH :: (FirstOrder b) => Vec r (Copi b v :-> v)
addManyH = Gen AddManyH

mulH :: Vec r (R :*: v :-> v)
mulH = Gen MulH

parH :: Vec r (u1 :-> v1) -> Vec r (u2 :-> v2) -> Vec r (u1 :+: u2 :-> v1 :+: v2)
parH f g = Gen $ ParH f g

kroneckerH :: Vec r (u1 :-> v1) -> Vec r (u2 :-> v2) -> Vec r (u1 :*: u2 :-> v1 :*: v2)
kroneckerH f g = Gen $ KroneckerH f g

swapH :: Vec r (u :*: v :-> v :*: u)
swapH = Gen SwapH

fanoutH :: (FirstOrder b) => Vec r (Copi b u :*: Copi b v :-> Copi b (u :*: v))
fanoutH = Gen FanoutH

fanoutPiCopiH :: (FirstOrder b) => Vec r (Pi b u :*: Copi b v :-> Copi b (u :*: v))
fanoutPiCopiH = Gen FanoutPiCopiH

freeTensorH :: (FirstOrder b, FirstOrder c) => Vec r (Free b :*: Free c :-> Free (b, c))
freeTensorH = Gen FreeTensorH

freeTensorInvH :: (FirstOrder b, FirstOrder c) => Vec r (Free (b, c) :-> Free b :*: Free c)
freeTensorInvH = Gen FreeTensorInvH

composeHomCopiH :: (FirstOrder b) => Vec r ((u :-> v) :*: Copi b u :-> Copi b v)
composeHomCopiH = Gen ComposeHomCopiH

curryCopiH :: Vec r (Copi (b, c) v :-> Copi b (Copi c v))
curryCopiH = Gen CurryCopiH

sum :: [Vec r v] -> Vec r v
sum = foldr (.+.) zero

linear :: (Gen r u -> Vec r v) -> Vec r u -> Vec r v
linear f Zero = zero
linear f (Add x y) = linear f x .+. linear f y
linear f (Mul r x) = r *. linear f x
linear f (Gen x) = f x

bilinear :: (Gen r u -> Gen r v -> Vec r w) -> Vec r u -> Vec r v -> Vec r w
bilinear f x y = linear (\x' -> linear (\y' -> f x' y') y) x

kronecker :: (Ring r) => (Vec r u -> Vec r u') -> (Vec r v -> Vec r v') -> Vec r (u :*: v) -> Vec r (u' :*: v')
kronecker f g = tensorExt $ \x y -> f x .*. g y

tassocLtr :: (Ring r) => Vec r ((u :*: v) :*: w) -> Vec r (u :*: (v :*: w))
tassocLtr = tensorExt . flip $ \z -> tensorExt $ \x y -> x .*. (y .*. z)

tassocRtl :: (Ring r) => Vec r (u :*: (v :*: w)) -> Vec r ((u :*: v) :*: w)
tassocRtl = tensorExt $ \x -> tensorExt $ \y z -> (x .*. y) .*. z

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

appPi :: Vec r (Pi a u) -> a -> Vec r u
appPi Zero = const Zero
appPi (Add x y) = \a -> Add (appPi x a) (appPi y a)
appPi (Mul r x) = \a -> Mul r (appPi x a)
appPi (Gen x) = fromPi x

instance Ring r => Num (Vec r R) where
    x + y = mkScalar $ getScalar x + getScalar y
    negate x= mkScalar $ negate (getScalar x)
    x * y = mkScalar $ getScalar x * getScalar y
    abs x = mkScalar $ abs (getScalar x)
    signum x = mkScalar $ signum (getScalar x)
    fromInteger x = mkScalar $ fromInteger x

class Eq b => FirstOrder b where
    inj :: b -> Vec r v -> Vec r (Copi b v)
    mapCopiGen :: (Ring r) => (b -> Vec r u -> Vec r v) -> Gen r (Copi b u) -> Vec r (Copi b v)
    collectGen :: (Ring r) => Gen r (Copi b v) -> Vec r v
    intersect :: (Ring r) => (b -> Vec r u -> Vec r v -> Vec r w) -> Vec r (Copi b u) -> Vec r (Copi b v) -> Vec r (Copi b w)
    decomposeCoprod :: (Ring r) => Vec r (Copi b v) -> [(b, Vec r v)]

mapCopi :: (Ring r, FirstOrder b) => (b -> Vec r u -> Vec r v) -> Vec r (Copi b u) -> Vec r (Copi b v)
mapCopi = linear . mapCopiGen

hmapCopi :: (Ring r, FirstOrder b) => (Vec r u -> Vec r v) -> Vec r (Copi b u) -> Vec r (Copi b v)
hmapCopi f = mapCopi (const f)

collect :: (Ring r, FirstOrder b)
    => Vec r (Copi b v) -> Vec r v
collect = linear collectGen

collect2 :: (Ring r, FirstOrder a, FirstOrder b)
    => Vec r (Copi a (Copi b v)) -> Vec r v
collect2 = collect . collect

collect3 :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c)
    => Vec r (Copi a (Copi b (Copi c v))) -> Vec r v
collect3 = collect . collect . collect

collect4 :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d)
    => Vec r (Copi a (Copi b (Copi c (Copi d v)))) -> Vec r v
collect4 = collect . collect . collect . collect

collect5 :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d, FirstOrder e) =>
    Vec r (Copi a (Copi b (Copi c (Copi d (Copi e v))))) -> Vec r v
collect5 = collect . collect . collect . collect . collect

collect6 :: (Ring r, FirstOrder a, FirstOrder b, FirstOrder c, FirstOrder d, FirstOrder e, FirstOrder f) =>
    Vec r (Copi a (Copi b (Copi c (Copi d (Copi e (Copi f v)))))) -> Vec r v
collect6 = collect . collect . collect . collect . collect . collect

bind :: (Gen r u -> Vec r v) -> (Vec r u -> Vec r v)
bind _ Zero = Zero
bind f (Add x y) = bind f x .+. bind f y
bind f (Mul r x) = r *. bind f x
bind f (Gen x) = f x

instance FirstOrder () where
    inj () x = Gen $ CopiUnit x
    mapCopiGen f (CopiUnit x) = Gen $ CopiUnit (f () x)
    collectGen (CopiUnit x) = x
    intersect f x y = Gen . CopiUnit $ f () (bind fromCopiUnit x) (bind fromCopiUnit y)
    decomposeCoprod x = [((), y) | let y = bind fromCopiUnit x, not (isNominallyZero y)]

canonicalCopiInt :: (Ring r) => r -> Vec r (Copi Int v) -> Gen r (Copi Int v)
canonicalCopiInt r Zero = CopiInt M.empty
canonicalCopiInt r (Add x y) = CopiInt $ M.unionWith (.+.) (fromCopiInt $ canonicalCopiInt r x) (fromCopiInt $ canonicalCopiInt r y)
canonicalCopiInt r (Mul r' x) = canonicalCopiInt (r * r') x
canonicalCopiInt 1 (Gen x) = x
canonicalCopiInt r (Gen x) = CopiInt $ M.map (r *.) (fromCopiInt x)

instance FirstOrder Int where
    inj b x = Gen . CopiInt $ M.singleton b x
    mapCopiGen f (CopiInt m) = Gen . CopiInt $ M.mapMaybeWithKey (\b -> zeroToNothing . f b) m
    collectGen (CopiInt m) = sum $ M.elems m
    intersect f x y = Gen . CopiInt $ M.intersectionWithKey f (fromCopiInt $ canonicalCopiInt 1 x) (fromCopiInt $ canonicalCopiInt 1 y)
    decomposeCoprod = M.toList . fromCopiInt . canonicalCopiInt 1

canonicalCopiChar :: (Ring r) => r -> Vec r (Copi Char v) -> Gen r (Copi Char v)
canonicalCopiChar r Zero = CopiChar M.empty
canonicalCopiChar r (Add x y) = CopiChar $ M.unionWith (.+.) (fromCopiChar $ canonicalCopiChar r x) (fromCopiChar $ canonicalCopiChar r y)
canonicalCopiChar r (Mul r' x) = canonicalCopiChar (r * r') x
canonicalCopiChar 1 (Gen x) = x
canonicalCopiChar r (Gen x) = CopiChar $ M.map (r *.) (fromCopiChar x)

instance FirstOrder Char where
    inj b x = Gen . CopiChar $ M.singleton (ord b) x
    mapCopiGen f (CopiChar m) = Gen . CopiChar $ M.mapMaybeWithKey (\b -> zeroToNothing . f (chr b)) m
    collectGen (CopiChar m) = sum $ M.elems m
    intersect f x y = Gen . CopiChar $ M.intersectionWithKey (f . chr) (fromCopiChar $ canonicalCopiChar 1 x) (fromCopiChar $ canonicalCopiChar 1 y)
    decomposeCoprod = map (chr *** id) . M.toList . fromCopiChar . canonicalCopiChar 1

partitionCopiSum :: Vec r (Copi (Either b c) v) -> (Vec r (Copi b v), Vec r (Copi c v))
partitionCopiSum Zero = (zero, zero)
partitionCopiSum (Add x y) = (xb .+. yb, xc .+. yc)
    where
        (xb, xc) = partitionCopiSum x
        (yb, yc) = partitionCopiSum y
partitionCopiSum (Mul r x) = (r *. xb, r *. xc)
    where
        (xb, xc) = partitionCopiSum x
partitionCopiSum (Gen (CopiSum xb xc)) = (xb, xc)

instance (FirstOrder b, FirstOrder c) => FirstOrder (Either b c) where
    inj (Left b) x = Gen $ CopiSum (inj b x) zero
    inj (Right c) x = Gen $ CopiSum zero (inj c x)
    mapCopiGen f (CopiSum x y) = Gen $ CopiSum (mapCopi (f . Left) x) (mapCopi (f . Right) y)
    collectGen (CopiSum x y) = collect x .+. collect y
    intersect f x y = Gen $ CopiSum (intersect (f . Left) xb yb) (intersect (f . Right) xc yc)
        where
            (xb, xc) = partitionCopiSum x
            (yb, yc) = partitionCopiSum y
    decomposeCoprod = uncurry (++) . (map (Left *** id) . decomposeCoprod *** map (Right *** id) . decomposeCoprod) . partitionCopiSum

curryCopiProd :: (Ring r) => Vec r (Copi (b, c) v) -> Vec r (Copi b (Copi c v))
curryCopiProd = linear go
    where
        go :: (Ring r) => Gen r (Copi (b, c) v) -> Vec r (Copi b (Copi c v))
        go (CopiProd x) = x

instance (FirstOrder b, FirstOrder c) => FirstOrder (b, c) where
    inj (b, c) x = Gen . CopiProd $ inj b (inj c x)
    mapCopiGen f x = Gen . CopiProd $ mapCopi (mapCopi . curry f) (curryCopiProd $ Gen x)
    collectGen (CopiProd x) = collect $ collect x
    intersect f x y = Gen . CopiProd $ intersect (intersect . curry f) (curryCopiProd x) (curryCopiProd y)
    decomposeCoprod x = [((b, c), z) | (b, y) <- decomposeCoprod (curryCopiProd x), (c, z) <- decomposeCoprod y]

partitionCopiList :: Vec r (Copi [b] v) -> (Vec r v, Vec r (Copi b (Copi [b] v)))
partitionCopiList Zero = (zero, zero)
partitionCopiList (Add x y) = (xNil .+. yNil, xCons .+. yCons)
    where
        (xNil, xCons) = partitionCopiList x
        (yNil, yCons) = partitionCopiList y
partitionCopiList (Mul r x) = (r *. xNil, r *. xCons)
    where
        (xNil, xCons) = partitionCopiList x
partitionCopiList (Gen (CopiPoly x xs)) = (x, xs)

instance (FirstOrder b) => FirstOrder [b] where
    inj [] x = Gen $ CopiPoly x zero
    inj (b : bs) x = Gen . CopiPoly zero $ inj b (inj bs x)
    mapCopiGen f (CopiPoly x xs) = Gen $ CopiPoly (f [] x) (mapCopi (\b -> mapCopi (f . (:) b)) xs)
    collectGen (CopiPoly x xs) = x .+. collect (collect xs)
    intersect f x y = Gen $ CopiPoly (f [] xh yh) (intersect (intersect . (f .) . (:)) xt yt)
        where
            (xh, xt) = partitionCopiList x
            (yh, yt) = partitionCopiList y
    decomposeCoprod x =
        [([], x0) | not (isNominallyZero x0)] ++
        [(b : bs, z) | (b, y) <- decomposeCoprod xs, (bs, z) <- decomposeCoprod y]
        where
            (x0, xs) = partitionCopiList x

instance (Ring r) => Eq (Vec r R) where
    a == b = getScalar a == getScalar b

instance (Ring r, FirstOrder b, Eq (Vec r v)) => Eq (Vec r (Copi b v)) where
    a == b = decomposeCoprod a == decomposeCoprod b

class ShowVec (v :: Space) where
    showsVec :: (Show r, Ring r) => Vec r v -> ShowS
    showsVec = showsPrecVec 0
    showsPrecVec :: (Show r, Ring r) => Int -> Vec r v -> ShowS
    showsPrecVec _ = showsVec

instance (Show r, Ring r, ShowVec v) => Show (Vec r v) where
    showsPrec = showsPrecVec

instance ShowVec R where
    showsPrecVec d = showsPrec d . getScalar

instance (Show b, FirstOrder b, ShowVec v) => ShowVec (Copi b v) where
    showsPrecVec d =
        showSum s d . decomposeCoprod
        where
            s d (b, x) = showParen (d > 10) $ showString "inj " . showsPrec 11 b . showString " " . showsPrec 11 x

instance (ShowVec v) => ShowVec (Pi b v) where
    showsPrecVec d x =
        showParen True $ showString "λ " . showsPrec 0 (appPi x undefined)

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
    rnfVec (Scalar r) = rnf r

instance (NFData a, FirstOrder a, NFVec v) => NFVec (Copi a v) where
    rnfVec = rnf . decomposeCoprod . Gen

instance (NFVec u, NFVec v) => NFVec (u :*: v) where
    rnfVec (Tensor x y) = rnf x `seq` rnf y
