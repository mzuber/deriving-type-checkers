{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.AbstractSyntax.C
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The library's default abstract syntax for container.
----------------------------------------------------------------------
module TypeCheckLib.AbstractSyntax.C ( -- * Container
                                       C (..),
                                       -- * Unification of containers
                                       unifyC,
                                       unifyCs,
                                       -- * Pretty printing
                                       ppC ) where

import TypeCheckLib.AbstractSyntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.AbstractSyntax.Def
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
--                             Container
-- ###################################################################

-- | Container encapsulate subcontainer and definitions. This data
-- structure provides according constructors for container, meta level
-- container for use in deduction rules and sequences and sets over
-- container.
data C = C    [C] [Def]         -- ^ Container
       | MC   String            -- ^ Meta level container
       | CSeq (Sequence C)      -- ^ Sequence over container
       | CSet (Set C)           -- ^ Set over container
         deriving (Show, Eq, Ord, Typeable)

-- TODO: Meta level function evaluating to a container


instance AST C where
    index (MC id) n = MC (id ++ show n)
    index (C cs ds) n = C (indexM cs n) (indexM ds n)
    index (CSeq s) n = CSeq (indexM s n)
    index (CSet s) n = CSet (indexM s n)

    (MC _) ~= c | isMeta c  = False
                | otherwise = True
    _      ~= _ = False
    
    isMeta (MC _) = True
    isMeta _      = False


$(deriveEvaluable ''C)

$(deriveSubstitutable ''C)

$(deriveInstantiable ''C)

$(deriveVars ''C)



-- ###################################################################
--                      Unification of containers
-- ###################################################################

instance Unifiable C where
    -- Unification of containers
    unify c1 c2 | c1 == c2         = (True, empty)
                | c1 `occursIn` c2 = (False, empty)
                | c2 `occursIn` c1 = (False, empty)
                | otherwise        = unifyC c1 c2

    -- Occurs check
    c  `occursIn` (C cs _) = foldr ((||) . (occursIn c)) False cs
    c  `occursIn` (CSeq (ObjSeq s)) = elem c s
    c  `occursIn` (CSet (ObjSet s)) = elem c s
    c1 `occursIn` c2 | c1 == c2  = True
                     | otherwise = False


-- | Unification of containers.
unifyC :: C -> C -> (Bool, Substitution)
unifyC (C cs1 ds1) (C cs2 ds2) = unifyCs cs1 cs2 `combine`
                                 unifyDs ds1 ds2

unifyC mc@(MC _) c = (True, singleton mc c)
unifyC c mc@(MC _) = unify mc c

unifyC (CSeq s1) (CSeq s2) = unify s1 s2
unifyC (CSet s1) (CSet s2) = unify s1 s2

unifyC _ _ = (False, empty)


-- | Unification of container lists.
unifyCs :: [C] -> [C] -> (Bool, Substitution)
unifyCs [] [] = (True, empty)
unifyCs _  [] = (False, empty)
unifyCs [] _  = (False, empty)
unifyCs cs1 cs2@((CSeq _):_) = unifyCs cs2 cs1
unifyCs cs1 cs2@((CSet _):_) = unifyCs cs2 cs1
unifyCs (x:xs) (y:ys) = let n        = length (y:ys) - length xs
                            (ys',zs) = splitAt n (y:ys)
                            seq      = CSeq (seqFromList ys')
                            set      = CSet (setFromList ys')
                        in case x of
                             CSeq _ -> unifyC x seq `combine`
                                       unifyCs xs zs
                             CSet _ -> unifyC x set `combine`
                                       unifyCs xs zs
                             _      -> unifyC x y `combine`
                                       unifyCs xs ys



-- ###################################################################
--                    Pretty printer for container
-- ###################################################################

ppC :: C -> String
ppC = PP.render . c2doc

-- TODO: Prettify pretty printer
c2doc :: C -> PP.Doc
-- useful for debug printing meta functions with containers as args
-- c2doc (C _ _) = PP.text "C"
c2doc (C cs ds) = let n = show (length cs)
                      csDocs = (PP.text (n ++ " Sub-containers:"))
                               :(map c2doc cs)
                      dsDocs = (PP.text "Definitions:")
                               :(map d2doc ds)
                  in PP.brackets (PP.text "Container:")
                     PP.$$ PP.nest 4
                           (PP.vcat csDocs PP.$$ PP.vcat dsDocs)
c2doc (MC id)  = PP.text id
c2doc (CSeq s) = PP.text "CSeq" PP.<+> PP.text (show s)
c2doc (CSet s) = PP.text "CSet" PP.<+> PP.text (show s)