module Main where

import System.Environment

import ModuleTheory.Tick
import ModuleTheory.Intersect
import ModuleTheory.Example

run "fast/3c/cube" = threeCycle intersectThreeCycle cube2
run "trad/3c/cube" = threeCycle traditionalIntersectThreeCycle cube2
run "fast/3c/caltrop" = threeCycle intersectThreeCycle caltrop2
run "trad/3c/caltrop" = threeCycle traditionalIntersectThreeCycle caltrop2
run "fast/4c/cube" = fourCycle intersectFourCycle cube2
run "trad/4c/cube" = fourCycle traditionalIntersectFourCycle cube2
run "fast/4c/caltrop" = fourCycle intersectFourCycle caltrop2
run "trad/4c/caltrop" = fourCycle traditionalIntersectFourCycle caltrop2
run "fast/4d/cube" = fourDense intersectFourDense cube3
run "trad/4d/cube" = fourDense traditionalIntersectFourDense cube3
run "fast/4d/caltrop" = fourDense intersectFourDense caltrop3
run "trad/4d/caltrop" = fourDense traditionalIntersectFourDense caltrop3
run "fast/4d/fin" = fourDense intersectFourDense fin3
run "trad/4d/fin" = fourDense traditionalIntersectFourDense fin3
run "fast/4t/cube" = fourTriangles intersectFourTriangles cube2
run "fast/4t/caltrop" = fourTriangles intersectFourTriangles caltrop2
run "trad/4t/cube" = fourTriangles traditionalIntersectFourTriangles cube2
run "trad/4t/caltrop" = fourTriangles traditionalIntersectFourTriangles caltrop2

main :: IO ()
main = do
    [implArg] <- getArgs
    let impl = run implArg
    mapM_ print $ asymptote impl 1
