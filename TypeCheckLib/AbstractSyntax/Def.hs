{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.AbstractSyntax.Def
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The library's default abstract syntax for definitions.
----------------------------------------------------------------------
module TypeCheckLib.AbstractSyntax.Def ( -- * Definitions
                                         Def (..),
                                         -- * Unification
                                         unifyD,
                                         unifyDs,
                                         -- * Pretty printing
                                         ppD,
                                         d2doc ) where

import TypeCheckLib.AbstractSyntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.Type
import TypeCheckLib.Evaluable
import TypeCheckLib.Substitution
import TypeCheckLib.Unification
import TypeCheckLib.Instantiation
import TypeCheckLib.Vars

import qualified Text.PrettyPrint as PP
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Prelude hiding (elem)
import Data.Foldable (elem)
import Data.Typeable


-- ###################################################################
--                            Definitions                                            
-- ###################################################################

-- | Definitions represent meta-level binder over terms. This data
-- structure provides constructors for definitions, meta level
-- definitions for use in deduction rules, sequences over definitions,
-- sets over definitions and meta level function calls evaluating to a
-- definition.
data Def = EmptyDef                  -- ^ Empty definition
         | Def   Ide Term            -- ^ Definition
         | DSeq  (Sequence Def)      -- ^ Sequence of definitions
         | DSet  (Set Def)           -- ^ Set of definitions
         | DFun  (MetaFun Def)       -- ^ Meta level function
         | MDef  String              -- ^ Meta level definition
           deriving (Show, Eq, Ord, Typeable)


instance AST Def where
    index (MDef id)   n = MDef (id ++ show n)
    index (Def ide t) n = Def (index ide n) (index t n)
    index (DSeq s)    n = DSeq (indexM s n)
    index (DSet s)    n = DSet (indexM s n)
    index (DFun f)    n = DFun (indexM f n)
    index EmptyDef    _ = EmptyDef

    (MDef _)    ~= d | isMeta d  = False
                     | otherwise = True
    _           ~= _         = False

    isMeta (MDef _)    = True
    isMeta _           = False


$(deriveEvaluable ''Def)

$(deriveSubstitutable ''Def)

$(deriveInstantiable ''Def)

$(deriveVars ''Def)



-- ###################################################################
--                     Unification of definitions
-- ###################################################################

instance Unifiable Def where
    -- Unification of definitions
    unify d1 d2 | d1 == d2         = (True, empty)
                | d1 `occursIn` d2 = (False, empty)
                | d2 `occursIn` d1 = (False, empty)
                | otherwise        = unifyD d1 d2

    -- Occurs Check
    d  `occursIn` (DSeq (ObjSeq s)) = elem d s
    d  `occursIn` (DSet (ObjSet s)) = elem d s
    d1 `occursIn` d2 | d1 == d2  = True
                     | otherwise = False


-- | Unification of definitions.
unifyD :: Def -> Def -> (Bool, Substitution)

-- unification of empty definitions
unifyD EmptyDef EmptyDef = (True, empty)

unifyD md@(MDef _) d = (True, singleton md d)
unifyD d md@(MDef _) = unifyD md d

-- unification of definitions
unifyD (Def ide1 t1) (Def ide2 t2) = unify ide1 ide2
                                     `combine` unify t1 t2

-- unification of meta and object level definition sequences
unifyD (DSeq s1) (DSeq s2) = unify s1 s2

-- unification of meta and object level definition sets
unifyD (DSet s1) (DSet s2) = unify s1 s2

-- otherwise
unifyD _ _ = (False, empty)


-- | Unification of definition lists.
unifyDs :: [Def] -> [Def] -> (Bool, Substitution)
unifyDs [] [] = (True, empty)
unifyDs _  [] = (False, empty)
unifyDs [] _  = (False, empty)
unifyDs ds1 ds2@((DSeq _):_) = unifyDs ds2 ds1
unifyDs ds1 ds2@((DSet _):_) = unifyDs ds2 ds1
unifyDs (x:xs) (y:ys) = let n        = length (y:ys) - length xs
                            (ys',zs) = splitAt n (y:ys)
                            seq      = DSeq (seqFromList ys')
                            set      = DSet (setFromList ys')
                        in case x of
                             DSeq _ -> unifyD x seq `combine`
                                       unifyDs xs zs
                             DSet _ -> unifyD x set `combine`
                                       unifyDs xs zs
                             _      -> unifyD x y `combine`
                                       unifyDs xs ys



-- ###################################################################
--                  Pretty printer for definitions
-- ###################################################################

ppD :: Def -> String
ppD = PP.render . d2doc

d2doc :: Def -> PP.Doc
d2doc EmptyDef     = PP.text "EmptyDef"
d2doc (Def ide t)  = PP.text (pprint ide) PP.<+>
                     PP.text "<=" PP.<+> t2doc t
d2doc (MDef id)    = PP.text id
d2doc (DSeq s)     = PP.text (show s)
d2doc (DSet s)     = PP.text (show s)
d2doc (DFun f)     = PP.text (pprint f)