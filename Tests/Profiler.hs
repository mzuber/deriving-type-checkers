module Main where

import Examples.FJChecker

-- TODO: Find better programs for profiling
main = do inferType "Tests/Programs/FJ/Subtyping.java"
          inferType "Tests/Programs/FJ/Pair2.java"
          inferType "Tests/Programs/FJ/Pair.java"