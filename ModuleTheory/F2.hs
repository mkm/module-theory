{-# LANGUAGE TypeOperators, DataKinds, TypeFamilies #-}
module ModuleTheory.F2 (
        F2,
    ) where

import ModuleTheory.Space
import ModuleTheory.Vector

newtype F2 = F2 Int
    deriving (Eq, Ord)

mkF2 :: Int -> F2
mkF2 = F2 . (`mod` 2)

instance Show F2 where
    show (F2 n) = show n

instance Num F2 where
    fromInteger = mkF2 . fromInteger
    F2 x + F2 y = mkF2 $ x + y
    F2 x * F2 y = mkF2 $ x * y
    abs = id
    signum = id
    negate = id

data instance Gen r (F2 :=> v) = CopowF2 (Vec r v) (Vec r v)

partitionCopowF2 :: Vec r (F2 :=> v) -> (Vec r v, Vec r v)
partitionCopowF2 Zero = (zero, zero)
partitionCopowF2 (Add x y) = (xb .+. yb, xc .+. yc)
    where
        (xb, xc) = partitionCopowF2 x
        (yb, yc) = partitionCopowF2 y
partitionCopowF2 (Mul r x) = (r *. xb, r *. xc)
    where
        (xb, xc) = partitionCopowF2 x
partitionCopowF2 (Gen (CopowF2 xb xc)) = (xb, xc)

instance FirstOrder F2 where
    inj 0 x = Gen $ CopowF2 x zero
    inj 1 x = Gen $ CopowF2 zero x
    mapCopowGen f (CopowF2 v0 v1) = Gen $ CopowF2 (f 0 v0) (f 1 v1)
    collectGen (CopowF2 v0 v1) = v0 .+. v1
    intersectCopow f x y = Gen $ CopowF2 (f 0 xb yb) (f 1 xc yc)
        where
            (xb, xc) = partitionCopowF2 x
            (yb, yc) = partitionCopowF2 y
    decomposeCopow = pair . partitionCopowF2
        where
            pair (Zero, Zero) = []
            pair (Zero, v1) = [(1, v1)]
            pair (v0, Zero) = [(0, v0)]
            pair (v0, v1) = [(0, v0), (1, v1)]
