module ModuleTheory.Polyset (
        IVec,
        Polyset,
        mkPolyset,
    ) where

import Prelude hiding (sum)
import ModuleTheory.Space
import ModuleTheory.Vector

type IVec = Vec Int
type Polyset a = IVec (Free a)

mkPolyset :: (FirstOrder a) => [a] -> Polyset a
mkPolyset = sum . map (`inj` 1)
