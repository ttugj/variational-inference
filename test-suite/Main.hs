{-# LANGUAGE UnicodeSyntax #-}

module Main where

import Control.Monad
import System.Exit
import VI.Test (allTests, doTests, withTolerance)


main ∷ IO ()
main = do
         (succ, fail) ← withTolerance 1.0e-4 $ doTests allTests
         let ns = length succ
             nf = length fail
         putStrLn $ show ns <> " succeeded, " <> show nf <> " failed."
         when (nf > 0) exitFailure

