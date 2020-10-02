{-# LANGUAGE TypeFamilies, DataKinds, GADTs, TypeOperators #-}
module ModuleTheory.Space (
        Space(..),
        Free,
        Cofree,
        Dual,
    ) where

import Data.Kind

-- | Classification of spaces (modules)
data Space :: Type where
    -- | Scalars.
    R :: Space
    -- | Coproduct.
    Copi :: Type -> Space -> Space
    -- | Product.
    Pi :: b -> Space -> Space
    -- | Direct sum.
    (:+:) :: Space -> Space -> Space
    -- | Tensor product.
    (:*:) :: Space -> Space -> Space
    -- | Polynomials.
    Poly :: Space -> Space
    -- | Linear maps.
    (:->) :: Space -> Space -> Space

infixr 6 :+:
infixr 7 :*:
infixr 1 :->

-- | A free module over 'b' is just a coproduct of 'b' copies of 'R'
type Free b = Copi b R
-- | A cofree module over 'b' is just a product of 'b' copies of 'R'
type Cofree b = Pi b R
type Dual v = v :-> R
