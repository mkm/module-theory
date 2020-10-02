module ModuleTheory.Tick (
        tick,
        analyseTicks,
        asymptote,
    ) where

import Data.IORef
import System.IO.Unsafe
import Control.DeepSeq
import Control.Exception

ticks :: IORef Int
ticks = unsafePerformIO $ newIORef 0

{-# NOINLINE tick #-}
tick :: a -> a
tick x = unsafePerformIO (modifyIORef' ticks (+ 1)) `seq` x

analyseTicks :: (NFData a) => a -> Int
analyseTicks x = unsafePerformIO $ do
    writeIORef ticks 0
    evaluate $ force x
    readIORef ticks

asymptote :: (NFData a) => (Int -> a) -> Int -> [Double]
asymptote f n = map trunc $ map (/ 2) ratios
    where
        ks = iterate (* 2) n
        ts = map (analyseTicks . f) ks
        ts' = map fromIntegral ts
        ratios = zipWith (/) (tail ts') ts'
        avgRatios = [ product (take 3 (drop m ratios)) ** (1 / 3) | m <- [0 ..]]
        trunc = (/ 1000) . fromIntegral . round . (* 1000)
