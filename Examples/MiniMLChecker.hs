----------------------------------------------------------------------
-- |
-- Module      :  Examples.MiniMLChecker
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Example type checker for Mini-ML.
----------------------------------------------------------------------
module Examples.MiniMLChecker where

import TypeCheckLib.Syntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.TypeChecker hiding (and, or)

import Examples.TypeSystems.MiniML
import Examples.Parser.MiniML

import Prelude hiding (abs, div, and, or, const)


-- | Mini-ML typing rules.
mlRules :: [Rule]
mlRules = [true, false, const, add, sub, mul, div, eqi, and, or,
           varpoly, abs, app, cond, pair, letpoly, letrec, fix]

-- | Compute type of Mini-ML expression.
computeType :: Term -> TypeCheckResult
computeType exp = computeTy defaultMode mlRules exp

-- | Check type of Mini-ML expression.
checkType :: Term -> Ty -> TypeCheckResult
checkType exp ty = checkTy defaultMode mlRules exp ty


-- | Infer the type of a Mini-ML expression.
inferType :: String -> IO ()
inferType exp = let res = computeType (parse exp)
                in case res of
                     Success ty  -> putStrLn (pprint ty)
                     Failure msg -> putStrLn msg
                     Error msg   -> putStrLn msg
                   
                      
-- | Infer the type of a Mini-ML expression given in a file.
inferTypeF :: String -> IO ()
inferTypeF fileName =
    do exp <- parseFromFile fileName
       let res = (computeType exp)
       case res of
         Failure msg -> putStrLn msg
         Success t   -> putStrLn (pprint t)
         Error msg   -> putStrLn msg