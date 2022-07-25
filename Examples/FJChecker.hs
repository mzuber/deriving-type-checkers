----------------------------------------------------------------------
-- |
-- Module      :  Examples.FJChecker
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Example type checker for FeatherweightJava.
----------------------------------------------------------------------
module Examples.FJChecker where

import TypeCheckLib.Syntax
import TypeCheckLib.TypeChecker

import Examples.Parser.FJ (parseExpr, parseFromFile, FJClass, FJExpr)
import Examples.Printer.FJ
import Examples.TypeSystems.FJ


-- | FeatherweightJava typing rules.
fjRules :: [FJClass] -> [Rule]
fjRules prg = [var, field prg, new prg, invoke prg, cast prg,
               method prg, constructor prg, fjclass prg]

---------------------------- Check expressions -----------------------

-- | Compute type of an FJ expression.
computeExprType ::  [FJClass] -> FJExpr -> TypeCheckResult
computeExprType prg exp = computeTy defaultMode (fjRules prg) exp

-- | Check type of an FJ expression.
checkExprType :: [FJClass] -> FJExpr -> Ty -> TypeCheckResult
checkExprType prg exp ty = checkTy defaultMode (fjRules prg) exp ty


-- | Inferr the type of a FJ expression given in a 'String'.
inferExprType :: String -> IO ()
inferExprType exp = do case computeExprType [] (parseExpr exp) of
                         Failure msg -> putStrLn msg
                         Success t   -> putStrLn (pprint t)
                         Error msg   -> putStrLn msg


----------------------------- Check classes --------------------------

-- | Compute type of an FJ expression.
computeType ::  [FJClass] -> FJClass -> TypeCheckResult
computeType prg c = computeTy defaultMode (fjRules prg) c

-- | Check type of an FJ expression.
checkType :: [FJClass] -> FJClass -> Ty -> TypeCheckResult
checkType prg c ty = checkTy defaultMode (fjRules prg) c ty

-- | Inferr the type of an FJ class given in a file.
inferType :: String -> IO ()
inferType fileName =
    do ast <- parseFromFile fileName
       let res = map (\ c -> case computeType ast c of
                               Failure msg -> msg
                               Success t   -> pprint  t
                               Error msg   -> msg) ast
       putStr $ (unlines res)