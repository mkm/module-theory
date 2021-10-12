module ModuleTheory.Polyset (
        IVec,
        Polyset,
        mkPolyset,
    ) where

import ModuleTheory.Space
import ModuleTheory.Vector
import ModuleTheory.Intersect

type IVec = Vec Int
type Polyset a = IVec (Free a)

mkPolyset :: (FirstOrder a) => [a] -> Polyset a
mkPolyset = sumList . map (`inj` 1)
