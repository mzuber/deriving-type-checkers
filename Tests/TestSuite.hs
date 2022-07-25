----------------------------------------------------------------------
-- |
-- Module      :  Tests.TestSuite
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for the type checker library.
----------------------------------------------------------------------
module Tests.TestSuite where

import Tests.Unification.TermUnification as T
import Tests.Unification.DefUnification as D
import Tests.Unification.TypeUnification as Ty
import Tests.TypeTests
import Tests.ConstraintGenerationTests as CG
import Tests.ConstraintSolvingTests as CS
import System.IO

runTests = do putStrLn "Running Substitution Tests ..."
              T.runAllApplyTests
              Ty.runApplyTyTests
              putStrLn "Running Unification Tests ..."
              T.runAllUnifyTests
              D.runAllUnifyTests
              Ty.runUnifyTyTests
              -- putStrLn "Running context tests ..."
              putStrLn "Running type tests ..."
              runAllTyTests
              putStrLn "Running Constraint Generation Tests ..."
              CG.runMiniMLInstTests
              CG.runFJInstTests
              putStrLn "Running Constraint Solving Tests ..."
              CS.runAllTests