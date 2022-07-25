{-# LANGUAGE FlexibleInstances #-}
----------------------------------------------------------------------
-- |
-- Module      :  Examples.Printer.FJ
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Pretty printer for FeatherweightJava.
----------------------------------------------------------------------
module Examples.Printer.FJ where

import Examples.Parser.FJ

import TypeCheckLib.Syntax
import Text.PrettyPrint

import Data.Foldable (toList)

-- ###################################################################
--                          Pretty Printer
-- ###################################################################

--------------------------- FJ Expressions ---------------------------
instance PrettyPrint FJExpr where
    pprint = render . ppE


ppE :: FJExpr -> Doc
ppE (Var ide) = text (pprint ide)

ppE (Invoke e1 e2) = case e1 of
                        Var _ -> ppE e1 <> char '.' <> ppE e2
                        _     -> parens (ppE e1) <>
                                 char '.' <> ppE e2

ppE (Meth ide (ObjSeq args)) = let argDocs = map ppE (toList args)
                               in text (pprint ide) <> parens
                                  (hcat (punctuate (comma <> space)
                                                   argDocs))
ppE (Meth ide args) = text (pprint ide) <> parens (text (pprint args))

ppE (New c (ObjSeq args)) = let argDocs = map ppE (toList args)
                            in text "new" <+> text (pprint c) <>
                               parens (hcat (punctuate
                                             (comma <> space)
                                             argDocs))
ppE (New c args) = text "new" <+> text (pprint c) <>
                   parens (text (pprint args))

ppE (Cast c e)       = parens (text (pprint c)) <+> ppE e
ppE (Assign lhs rhs) = ppE lhs <> equals <> ppE rhs <> semi
ppE (Return e)       = text "return" <+> ppE e <> semi
ppE (MExpr ide)      = text ide


----------------------------- FJ Methods -----------------------------

instance PrettyPrint FJMethod where
    pprint = render . ppM


ppM :: FJMethod -> Doc
ppM (MM ide) = text ide
ppM (M rt m ps b) = text (pprint rt) <+> text (pprint m) <+>
                    parens pPs <+> lbrace $+$ nest 4 (ppE b) $$ rbrace
    where
      pPs = case ps of
              ObjSeq s    -> hcat $ punctuate
                             (comma <> space) (map ppP (toList s))
              MetaSeq _ _ -> text (pprint ps)

ppP :: (Ty, FJExpr) -> Doc
ppP (c,x) = text (pprint c) <+> ppE x


--------------------------- FJ Constructors --------------------------

instance PrettyPrint FJConstructor where
    pprint = render . ppC


ppC :: FJConstructor -> Doc
ppC (C c ps s as) = text (pprint c) <+>
                    parens pPs <+> lbrace $+$ nest 4 (vcat pB) $$ rbrace
    where
      pPs = case ps of
              ObjSeq s    -> hcat $ punctuate
                             (comma <> space) (map ppP (toList s))
              MetaSeq _ _ -> text (pprint ps)
      pAs = case as of
              ObjSeq s    -> map ppE (toList s)
              MetaSeq _ _ -> [text (pprint as)]
      pB  = (ppE s <> semi) : pAs

ppC (MC ide) = text ide


----------------------------- FJ Classes -----------------------------
instance PrettyPrint FJClass where
    pprint = render . ppCl

instance PrettyPrint [FJClass] where
    pprint = render . ppCls
    -- for testing and debugging of meta level
    -- functions with classes as arguments
    -- pprint = const "program"


ppCls :: [FJClass] -> Doc
ppCls []  = text "{}"
ppCls prg = vcat . (map ppCl) $ prg

ppCl :: FJClass -> Doc
ppCl (Class c d as k ms) = text "class" <+> text (pprint c) <+>
                           text "extends" <+> text (pprint d) <+>
                           lbrace $+$ nest 4 (pAs <> text "\n" $$
                                              ppC k <> text "\n" $$
                                              pMs) $$ rbrace
        where
          pAs = case as of
                  ObjSeq s    -> vcat $ map ppA (toList s)
                  MetaSeq _ _ -> text (pprint as)

          ppA (ty,v) = text (pprint ty) <+> ppE v <> semi

          pMs = case ms of
                  ObjSeq s    -> vcat $ map ppM (toList s)
                  MetaSeq _ _ -> text (pprint ms)
