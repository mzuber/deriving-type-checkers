----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Combinators
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- This module provides a set of combinators which allow a more
-- convenient notion to define judgements, constraints, sets, and
-- sequences.
----------------------------------------------------------------------
module TypeCheckLib.Combinators ( -- * Define constraints
                                  (=:=)
                                , not
                                , (=/=)
                                , (∧)
                                , and
                                , (∨)
                                , or
                                , (<?>)
                                , (<|>)
                                  -- * Define judgements
                                , (⊢)
                                , (|-)
                                , (<:>)                                  
                                ) where

import TypeCheckLib.AbstractSyntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.AbstractSyntax.Def
import TypeCheckLib.AbstractSyntax.C (C (CSeq, CSet))
import TypeCheckLib.Type
import TypeCheckLib.Rule
import TypeCheckLib.Context
import TypeCheckLib.Evaluable
import TypeCheckLib.Substitution
import TypeCheckLib.Unification
import TypeCheckLib.Instantiation
import TypeCheckLib.Vars

import Prelude hiding (not, and, or)
import Data.Typeable



-- | Equality constraint.
infix 6 =:=
(=:=) :: Eq a => a -> a -> Constraint a
c =:= d = Eq c d (mkErr "Error: could not solve equality constraint.")

-- | Negate a given constraint.
not :: Eq a => Constraint a -> Constraint a
not c = Not c (mkErr "Error: could not solve negated constraint.")

-- | Inequality constraint.
infix 6 =/=
(=/=) :: Eq a => a -> a -> Constraint a
c =/= d = Not (Eq c d (mkErr "Error"))
              (mkErr "Error: could not solve inequality constraint.")

-- | Conjunction of constraints (UTF8-based).
infix 6 ∧
(∧) :: Eq a => Constraint a -> Constraint a -> Constraint a
c ∧ d = And c d
        (mkErr "Error: could not solve conjunction of constraints.")

-- | Conjunction of constraints (ASCII-based).
and :: Eq a => Constraint a -> Constraint a -> Constraint a
x `and` y = x ∧ y
 
-- | Disjunction of constraints (UTF8-based).
infix 6 ∨
(∨) :: Eq a => Constraint a -> Constraint a -> Constraint a
c ∨ d = Or c d
        (mkErr "Error: could not solve disjunction of constraints.")

-- | Disjunction of constraints (ASCII-based).
or :: Eq a => Constraint a -> Constraint a -> Constraint a
x `or` y = x ∨ y

-- | Conditional constraint.
infix 6 <?>
(<?>) :: Eq a => Constraint a -> Constraint a -> Constraint a
c <?> b = If c b
          (mkErr "Error: could not solve conditional constraint.")




-- | Add a specific error message to a given constraint
-- and lift the resulting constraint to a judgement.
infix 5 <|>
(<|>) :: ( Show a, AST a, PrettyPrint a, Evaluable a, Vars a,
           Instantiable a, Unifiable a, Substitutable a ) =>
         Constraint a -> ErrorMsg -> Judgement
c <|> err = C (replaceErr c err)


-- | Syntactic sugar for the definition of judgements. The turnstile
-- function and the '<:>' function can be used to define a judgement
-- more conveniently.
infix 5 ⊢
(⊢) :: ( Show a, Eq a, Ord a, PrettyPrint a, Typeable a, AST a, Vars a,
         Evaluable a, Substitutable a, Unifiable a, Instantiable a ) =>
       Context -> (a, Ty) -> Judgement
cxt ⊢ (exp,ty) = J cxt exp ty

infix 5 |-
(|-) :: ( Show a, Eq a, Ord a, PrettyPrint a, Typeable a, AST a, Vars a,
          Evaluable a, Substitutable a, Unifiable a, Instantiable a ) =>
        Context -> (a, Ty) -> Judgement
(|-) = (⊢)

infix 6 <:>
(<:>) :: ( Show a, Eq a, Ord a, Typeable a, AST a, Evaluable a,
           Substitutable a, Unifiable a, Instantiable a ) =>
         a -> Ty -> (a, Ty)
exp <:> ty = (exp,ty)