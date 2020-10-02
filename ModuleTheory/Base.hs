{-# LANGUAGE GADTs #-}
module ModuleTheory.Base (
        fromBaseList,
        fromWeightedBaseList,
        toWeightedBaseList,
    ) where

import Prelude hiding (sum)
import Data.Char
import qualified Data.IntMap as M

import ModuleTheory.Vector

instance Base K where
    baseFold ZeroV f k = id
    baseFold (AddV x y) f k = baseFold x f k . baseFold y f k
    baseFold (MulV k' x) f k = baseFold x f (k * k')
    baseFold (InjV b) f k = f b k
    baseFold (ScalarV k') f k = f K (k * k')

    measure ZeroV = 0
    measure (AddV x y) = measure x + measure y
    measure (MulV k x) = k * measure x
    measure (InjV _) = 1
    measure (ScalarV k) = k

instance Base Int where
    baseFold ZeroV f k = id
    baseFold (AddV x y) f k = baseFold x f k . baseFold y f k
    baseFold (MulV k' x) f k = baseFold x f (k * k')
    baseFold (InjV b) f k = f b k

    measure ZeroV = 0
    measure (AddV x y) = measure x + measure y
    measure (MulV k x) = k * measure x
    measure (InjV _) = 1

instance Base Char where
    baseFold ZeroV f k = id
    baseFold (AddV x y) f k = baseFold x f k . baseFold y f k
    baseFold (MulV k' x) f k = baseFold x f (k * k')
    baseFold (InjV b) f k = f b k

    measure ZeroV = 0
    measure (AddV x y) = measure x + measure y
    measure (MulV k x) = k * measure x
    measure (InjV _) = 1

instance Base (Vec k b) where
    baseFold ZeroV f k = id
    baseFold (AddV x y) f k = baseFold x f k . baseFold y f k
    baseFold (MulV k' x) f k = baseFold x f (k * k')
    baseFold (InjV b) f k = f b k

    measure ZeroV = 0
    measure (AddV x y) = measure x + measure y
    measure (MulV k x) = k * measure x
    measure (InjV _) = 1

instance (Base b, Base c) => Base (b, c) where
    baseFold ZeroV f k = id
    baseFold (AddV x y) f k = baseFold x f k . baseFold y f k
    baseFold (MulV k' x) f k = baseFold x f (k * k')
    baseFold (InjV b) f k = f b k
    baseFold (TensorV x y) f k = baseFold x (\b -> baseFold y (curry f b)) k

    measure ZeroV = 0
    measure (AddV x y) = measure x + measure y
    measure (MulV k x) = k * measure x
    measure (InjV _) = 1
    measure (TensorV x y) = measure x * measure y

instance (Base b, Base c) => Base (Either b c) where
    baseFold ZeroV f k = id
    baseFold (AddV x y) f k = baseFold x f k . baseFold y f k
    baseFold (MulV k' x) f k = baseFold x f (k * k')
    baseFold (InjV b) f k = f b k
    baseFold (SumV x y) f k = baseFold x (f . Left) k . baseFold y (f . Right) k

    measure ZeroV = 0
    measure (AddV x y) = measure x + measure y
    measure (MulV k x) = k * measure x
    measure (InjV _) = 1

instance (Base b) => Base [b] where
    baseFold ZeroV f k = id
    baseFold (AddV x y) f k = baseFold x f k . baseFold y f k
    baseFold (MulV k' x) f k = baseFold x f (k * k')
    baseFold (InjV b) f k = f b k
    baseFold (PolySingleV x) f k = baseFold x (f . pure) k
    baseFold (PolyMulV x) f k = baseFold x (f . uncurry (++)) k

    measure ZeroV = 0
    measure (AddV x y) = measure x + measure y
    measure (MulV k x) = k * measure x
    measure (InjV _) = 1

instance (Base c) => Base (CHom b c) where
    baseFold ZeroV f k = id
    baseFold (AddV x y) f k = baseFold x f k . baseFold y f k
    baseFold (MulV k' x) f k = baseFold x f (k * k')
    baseFold (InjV b) f k = f b k
    baseFold (SingleC b x) f k = baseFold x (f . singleCHom b) k
    baseFold (ScalarC x) f k = baseFold x (f . ScalarMap) k
    baseFold (IntC m) f k = \r -> M.foldrWithKey (\b x -> baseFold x (f . IntMap b) k) r m
    baseFold (CharC m) f k = \r -> M.foldrWithKey (\b x -> baseFold x (f . CharMap (chr b)) k) r m
    baseFold (ProdC g) f k = baseFold g (f . ProdMap) k
    baseFold (SumC g h) f k = baseFold g (f . LeftMap) k . baseFold h (f . RightMap) k
    baseFold (PolyC g) f k = baseFold g (f . PolyMap) k
    baseFold (VecC g) f k = baseFold g (f . VecMap) k

    measure ZeroV = 0
    measure (AddV x y) = measure x + measure y
    measure (MulV k x) = k * measure x
    measure (InjV _) = 1

fromBaseList :: (Ring k) => [b] -> Vec k b
fromBaseList = sum . map inj

fromWeightedBaseList :: (Ring k) => [(b, k)] -> Vec k b
fromWeightedBaseList = sum . map (\(b, k) -> k *. inj b)

toWeightedBaseList :: (Ring k, Base b) => Vec k b -> [(b, k)]
toWeightedBaseList x = baseFold x (\b k r -> (b, k) : r) 1 []
