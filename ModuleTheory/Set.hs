module ModuleTheory.Set (
        B,
        BVec,
        Set,
        mkSet,
    ) where

import ModuleTheory.Space
import ModuleTheory.Vector
import ModuleTheory.Intersect

data B = O | I
    deriving (Eq)

type BVec = Vec B
type Set a = BVec (Free a)

instance Show B where
    show O = "0"
    show I = "1"

instance Num B where
    O + O = O
    _ + _ = I

    negate _ = undefined

    I * I = I
    _ * _ = O

    abs = id
    signum = id

    fromInteger n
        | n > 0 = I
        | n == 0 = O
        | otherwise = undefined

mkSet :: (FirstOrder a) => [a] -> Set a
mkSet = sumList . map (`inj` 1)
