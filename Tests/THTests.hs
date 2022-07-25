{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
{-# OPTIONS_GHC -ddump-splices #-}
module Tests.THTests where

import TypeCheckLib.AbstractSyntax hiding (pprint)
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.AbstractSyntax.Def
import TypeCheckLib.AbstractSyntax.C
import TypeCheckLib.Evaluable
import TypeCheckLib.Substitution
import TypeCheckLib.Instantiation
import TypeCheckLib.Unification
import TypeCheckLib.Vars
import TypeCheckLib.THUtil

import Language.Haskell.TH
import Data.Typeable


data T = T String                  -- ^ Type
       | TV String                 -- ^ Type variable
       | TF T T                    -- ^ Function type
       | TT3 T T T                 -- ^ Ternary tuple type
       | T :|: T                   -- ^ Infix constructor
       | TSeq (Sequence T)         -- ^ Type sequence
       | TMF (MetaFun T)           -- ^ Meta level function
       | TMFR {f :: MetaFun T}     -- ^ Meta level function in record
       | MT String                 -- ^ Meta level type
         deriving (Show, Eq, Ord, Typeable)

instance AST T where
    index (MT id)  n = MT (id ++ show n)
    index (TF s t) n = TF (index s n) (index t n)
    index t        _ = t

    (MT _) ~= (MT _) = False
    (MT _) ~= _      = True
    _      ~= _      = False

    isMeta (MT _) = True
    isMeta _      = False


test1 = $(stringE . show =<< isClassInstance ''AST [ConT ''T])

$(deriveEvaluable ''T)
{-
test2 = $(stringE . pprint =<< deriveEvaluable ''T)

test3 = $(stringE . pprint =<< deriveSubstitutable ''T)

$(deriveSubstitutable ''T)

test4 = $(stringE . pprint =<< deriveInstantiable ''T)

$(deriveInstantiable ''T)

isMFTest = $(stringE =<< do TyConI (DataD _ name _ cs _) <- reify ''T
                            let cs' = map (isMF (ConT name)) cs
                            return (show cs'))

test5 = $(stringE . pprint =<< deriveEvaluable ''Term)

test6 = $(stringE . pprint =<< deriveSubstitutable ''Term)

test7 = $(stringE . pprint =<< deriveUnifiable ''T)

$(deriveUnifiable ''T)

$(deriveVars ''T)
-}