----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.TypeChecker
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- This module defines the user interface to the type checker
-- library. It provides functions for computing and checking types
-- for user-defined expressions.
----------------------------------------------------------------------
module TypeCheckLib.TypeChecker ( -- * Type check results
                                  TypeCheckResult (..)
                                  -- * Type check modes
                                , TypeCheckMode (..)
                                , defaultMode
                                , debugMode
                                  -- * Compute and check types
                                , computeTy
                                , checkTy
                                  -- * Type rules
                                , Rule (..)
                                  -- ** Judgements
                                , Judgement (J, C, JSeq)
                                , (⊢)
                                , (|-)
                                , (<:>)
                                  -- ** Contexts
                                , Context (..)
                                , Ctx.empty
                                , Ctx.insert
                                , Ctx.singleton
                                , Ctx.fromList
                                , Ctx.fromSeq
                                , Ctx.delete
                                , Ctx.lkup
                                , Ctx.union
                                , mInsertCtx
                                , mDeleteCtx
                                , (!)
                                , gen
                                -- ** Constraints
                                , Constraint (..)
                                , (=:=)
                                , not
                                , (=/=)
                                , (∧)
                                , and
                                , (∨)
                                , or
                                , (<?>)
                                , (<|>)
                                  -- ** Error messages for constraints
                                , ErrorMsg (..)
                                , mkErr
                                , mkMsg
                                ) where

import TypeCheckLib.Syntax
import TypeCheckLib.Context as Ctx
import TypeCheckLib.Rule
import TypeCheckLib.Combinators
import TypeCheckLib.ConstraintGeneration as CG
import qualified TypeCheckLib.ConstraintSolving as CS

import Data.Typeable
import Prelude hiding (not, and, or)


-- | Result of the 'computeType' and 'checkType' functions.
data TypeCheckResult = Success Ty
                     | Failure String
                     | Error String
                       deriving Show


-- | The type check mode allows the user to supply additional
-- informations for the computation of an expression's type,
-- such as a specific context.
data TypeCheckMode = TypeCheckMode { initialCtx :: Context
                                   , debug :: Bool
                                   }


-- | The default type check mode consists of an empty context.
defaultMode :: TypeCheckMode
defaultMode = TypeCheckMode Ctx.empty False


-- | The debug type check mode provides an empty context and enables
-- debugging.
debugMode :: TypeCheckMode
debugMode = TypeCheckMode Ctx.empty True


-- | Compute the type of an expression
-- based on a given set of typing rules.
computeTy :: (Show a, AST a, Substitutable a, Evaluable a,
              Unifiable a, Instantiable a, PrettyPrint a, Vars a) =>
             TypeCheckMode    -- ^ Inital context
          -> [Rule]           -- ^ Typing rules
          -> a                -- ^ Expression
          -> TypeCheckResult
computeTy mode rs exp =
    evalTypeCheckM $
    do tv <- freshTV
       let j   = J (initialCtx mode) exp tv
           dbg = debug mode
       cs <- CG.genCs rs j dbg
       return $ case (CS.solveCs cs) of
                  CS.Success o     -> Success (o .@. tv)
                  CS.NoRuleFound j -> Failure $
                                      "No matching rule found for:\n" ++ pprint j
                  CS.Failure (C c) -> Failure $ mkMsg (err c)
                  CS.Error msg     -> Error msg



-- | Compute the type of a given expression and check if
-- the computed type is an instance of the given one.
checkTy :: (Show a, AST a, Substitutable a, Evaluable a,
            Unifiable a, Instantiable a, PrettyPrint a, Vars a) =>
           TypeCheckMode       -- ^ Inital context
        -> [Rule]              -- ^ Typing rules
        -> a                   -- ^ Expression
        -> Ty                  -- ^ Type
        -> TypeCheckResult

checkTy mode rs exp ty = case computeTy mode rs exp of
                           Success ty' -> compTys ty ty' exp
                           res         -> res

-- | The computed type of an expression can be more general than the
-- given one.  'compTys' checks whether the given type is an instance
-- of the computed one or if the two types are equal.
compTys :: Ty    -- ^ Given type
        -> Ty    -- ^ Computed type
        -> b     -- ^ Expression for which the type was computed
        -> TypeCheckResult
compTys gTy cTy exp =
    let (b,o) = unify gTy cTy
        cTy'  = o .@. cTy
    in if b && (gTy == cTy') then Success cTy
       else Failure ("Couldn't match expected type `" ++ pprint gTy ++
                     "' against inferred type `" ++ pprint cTy ++ "'")


-- Syntactic sugar  for judgement and constraint sequences
instance SequenceSugar Judgement where
    mSeq i j = JSeq (MetaSeq (MetaISet i) j)

instance Eq a => SequenceSugar (Constraint a) where
    mSeq i c = ConstraintSeq (MetaSeq (MetaISet i) c)
               (mkErr "Error: could not solve sequence of constraints.")