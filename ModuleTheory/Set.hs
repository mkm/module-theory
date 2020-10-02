module ModuleTheory.Set (
        B,
        BVec,
        Set,
        mkSet,
    ) where

import Prelude hiding (sum)
import ModuleTheory.Space
import ModuleTheory.Vector

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
mkSet = sum . map (`inj` 1)
