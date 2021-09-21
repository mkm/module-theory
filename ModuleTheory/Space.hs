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
    Copow :: Type -> Space -> Space
    -- | Product.
    Pow :: Type -> Space -> Space
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

-- | A free module over 'b' is just a copower of 'b' copies of 'R'.
type Free b = Copow b R
-- | A cofree module over 'b' is just a power of 'b' copies of 'R'.
type Cofree b = Pow b R
-- | The dual of a module consists of scalar valued maps out of the module.
type Dual v = v :-> R
