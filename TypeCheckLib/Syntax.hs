----------------------------------------------------------------------
-- |
-- Module      :  TypeCHeckLib.Syntax
-- Copyright   :  (c) 2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- The library's components for abstract syntax and types.
----------------------------------------------------------------------
module TypeCheckLib.Syntax ( -- * Abstract Syntax
                             AST (..)
                             -- ** Identifiers
                           , Identifier (..)
                           , Ide
                             -- ** Sequences
                           , ISet (..)
                           , Sequence (..)
                           , emptySeq
                           , seqFromList
                           , mseq
                           , SequenceSugar (mSeq)
                             -- ** Sets
                           , Set (..)
                           , emptySet
                           , union
                           , diff
                           , (\\)
                           , setFromList
                           , setFromSeq
                           , mset
                           , SetSugar (mSet)
                             -- ** Meta level functions
                           , MetaFun (..)
                             -- ** Auxiliary functions
                           , uncurry3
                           , uncurry4
                           , uncurry5
                           , uncurry6
                           , uncurry7
                             -- ** Pretty Printing
                           , PrettyPrint (pprint)
                             -- * Types
                           , Ty (..)
                           , Vars (..)
                           , deriveVars
                             -- ** Auxilary functions on types
                           , (->:)
                           , (×)
                           , (**)
                           , mkT
                           , mkTV
                           , genInstOf
                           , (>=)
                             -- ** Type checking monad
                           , TypeCheckM
                           , freshTV
                           , evalTypeCheckM
                             -- * Substitutions
                           , Substitutable (apply)
                           , (.@.)
                           , (.*.)
                           , deriveSubstitutable
                           , Substitution
                           , empty
                           , singleton
                           , lkup
                           , insert
                           , compose
                             -- * Evaluation of meta level functions
                           , Evaluable (..)
                           , deriveEvaluable
                             -- * Instantiation
                           , Instantiable (..)
                           , deriveInstantiable
                             -- * Unification Framework
                           , Unifiable (..)
                           , combine
                           , (.~.)
                           , deriveUnifiable
                           ) where

import TypeCheckLib.AbstractSyntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.AbstractSyntax.Def
import TypeCheckLib.AbstractSyntax.C
import TypeCheckLib.Type
import TypeCheckLib.Substitution
import TypeCheckLib.Evaluable
import TypeCheckLib.Instantiation
import TypeCheckLib.Unification
import TypeCheckLib.Vars
import TypeCheckLib.Combinators

import Prelude hiding ((**), (>=))


-- | Type class providing syntactic sugar for
-- the definition of meta level sequences.
class SequenceSugar a where
    mSeq :: String -> a -> a

instance SequenceSugar Term where
    mSeq i t = TSeq (MetaSeq (MetaISet i) t)
	
instance SequenceSugar Def where
    mSeq i d = DSeq (MetaSeq (MetaISet i) d)
	
instance SequenceSugar C where
    mSeq i c = CSeq (MetaSeq (MetaISet i) c)

instance SequenceSugar Ty where
    mSeq i ty = TySeq (MetaSeq (MetaISet i) ty)



-- | Type class providing syntactic sugar
-- for the definition of meta level sets.
class SetSugar a where
    mSet :: String -> a -> a

instance SetSugar Term where
    mSet i t = TSet (MetaSet (MetaISet i) t)
	
instance SetSugar Def where
    mSet i d = DSet (MetaSet (MetaISet i) d)
	
instance SetSugar C where
    mSet i c = CSet (MetaSet (MetaISet i) c)

instance SetSugar Ty where
    mSet i ty = TySet (MetaSet (MetaISet i) ty)