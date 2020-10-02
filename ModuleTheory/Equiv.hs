{-# LANGUAGE RankNTypes #-}
module ModuleTheory.Equiv (
        toCanonicalCHom,
        toCanonicalWeightedBaseList,
    ) where

import Data.Word

import ModuleTheory.Vector
import ModuleTheory.Base
import ModuleTheory.Eval

instance Equiv K where
    mkCompactH = MkScalarH # TensorFstIdH
    singleCHom K = ScalarMap

instance Equiv Int where
    mkCompactH = MkIntH
    singleCHom = IntMap

instance Equiv Char where
    mkCompactH = MkCharH
    singleCHom = CharMap

instance (Equiv a1, Equiv a2) => Equiv (a1, a2) where
    mkCompactH = UncurryH # MapH MkCHomH # MkCHomH # TensorAssocH
    singleCHom (a1, a2) = ProdMap . singleCHom a1 . singleCHom a2

instance (Equiv a1, Equiv a2) => Equiv (Either a1 a2) where
    mkCompactH = MkSumH # MkCHomH .|. MkCHomH # tensorDistH
    singleCHom (Left a) = LeftMap . singleCHom a
    singleCHom (Right a) = RightMap . singleCHom a

instance Equiv a => Equiv [a] where
    mkCompactH = MkPolyH # MkCHomH # UnconsH .&. IdH
    singleCHom [] = PolyMap . singleCHom (Left K)
    singleCHom (a : as) = PolyMap . singleCHom (Right (a, as))

instance (Ring k, Base b, Equiv b) => Eq (Vec k b) where
    x == y = isZero (x .-. y)

instance (Ring k, Base k, Equiv k, Base b, Equiv b) => Equiv (Vec k b) where
    mkCompactH = MkVecH # MkCHomH # BaseToBaseH toCanonicalWeightedBaseList .&. IdH
    singleCHom x = VecMap . singleCHom (toCanonicalWeightedBaseList x)

toCanonicalCHom :: (Ring k, Equiv b) => Vec k (Hom b (CHom b K))
toCanonicalCHom = MapH measureH # MkCHomH # TensorRevSndIdH

toCanonicalWeightedBaseList :: (Ring k, Base b, Equiv b) => Vec k b -> [(b, k)]
toCanonicalWeightedBaseList = toWeightedBaseList . evh (TensorSndIdH # assocsH # toCanonicalCHom)

isZero :: (Ring k, Base b, Equiv b) => Vec k b -> Bool
isZero = null . toCanonicalWeightedBaseList

instance (Ring k, Show k, Equiv b, Base b, Show b) => Show (Vec k b) where
    show = show . toCanonicalWeightedBaseList
