{-# LANGUAGE DataKinds, TypeOperators #-}
module ESOP where

import ModuleTheory.Space
import ModuleTheory.Vector
import ModuleTheory.Intersect

-- 2.4 Meet the Modules

f :: (Ring r) => Vec r R -> Vec r R
f = linear $ \One -> 42

g :: (Ring r) => Vec r (Free String) -> Vec r (Free String)
g = freeExt $ single . reverse

containsFoo :: (Ring r) => Vec r (CFree String) -> Vec r R
containsFoo = cfreeExt 1 (\s -> if s == "foo" then 1 else 0)

indexByLength :: (Ring r) => Vec r (Free String) -> Vec r (Copow Int (Free String))
indexByLength = freeExt $ \s -> inj (length s) (single s)

-- 3 Linear Algebra as a Query Language

σ :: (Ring r, FirstOrder a) => (a -> Bool) -> Vec r (Free a) -> Vec r (Free a)
σ p = freeExt $ \a -> if p a then single a else zero

π₁ :: (Ring r, FirstOrder b) => Vec r (Free a :*: Free b) -> Vec r (Free a)
π₁ = tensorExt $ \u v -> u .* weight v

π₂ :: (Ring r, FirstOrder a) => Vec r (Free a :*: Free b) -> Vec r (Free b)
π₂ = tensorExt $ \u v -> weight u *. v

π₁₃ :: (Ring r, FirstOrder b) => Vec r (Free a :*: (Free b :*: Free c)) -> Vec r (Free a :*: Free c)
π₁₃ = mapTensor id π₂

α :: (Ring r) => Vec r (u :*: (v :*: w)) -> Vec r ((u :*: v) :*: w)
α = tensorExt $ \u -> tensorExt $ \v w -> (u .*. v) .*. w

β :: (Ring r) => Vec r (u :*: v) -> Vec r (v :*: u)
β = tensorExt $ \u v -> v .*. u

x :: Vec r (Free String :*: Free Int)
x = single "a" .*. single 1 .+. single "b" .*. single 2 .+. single "c" .*. single 3

y :: Vec r (Free Int :*: Free String)
y = single 2 .*. single "p" .+. single 3 .*. single "q" .+. single 4 .*. single "r"

x' :: (Ring r) => Vec r (CFree String :*: CFree Int :*: CFree String)
x' = csingle "a" .*. csingle 1 .*. 1 .+. csingle "b" .*. csingle 2 .*. 1 .+. csingle "c" .*. csingle 3 .*. 1

y' :: (Ring r) => Vec r (CFree String :*: CFree Int :*: CFree String)
y' = 1 .*. csingle 2 .*. csingle "p" .+. 1 .*. csingle 3 .*. csingle "q" .+. 1 .*. csingle 4 .*. csingle "r"
