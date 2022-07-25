----------------------------------------------------------------------
-- |
-- Module      :  Examples.Printer.MiniML
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Pretty printer for Mini-ML.
----------------------------------------------------------------------
module Examples.Printer.MiniML where

import TypeCheckLib.AbstractSyntax
import TypeCheckLib.AbstractSyntax.Term

import Text.PrettyPrint

-- | Pretty printer for terms encoding MiniML.
instance PrettyPrint Term where
    pprint = render . pp


pp :: Term -> Doc
pp (Var ide)   = text (pprint ide)
pp (Const n)   = integer n
pp (MConst id) = text id
pp (Char c)    = char c
pp (MChar id)  = text id
pp (Bind x t)  = (pp t) <> colon <> text (pprint x)

pp (K Tuple 2 (t1:t2:[])) = parens (pp t1 <> comma <> space <> pp t2)

pp (K Let 3 (t1:t2:t3:[])) = text "let" <+> pp t1 <+> equals <+>
                             pp t2 $$ text "in" <+> pp t3

pp (K LetRec 3 (t1:t2:t3:[])) = text "letrec" <+> pp t1 <+> equals
                                <+> pp t2 $$ text "in" <+> pp t3

pp (K App 2 [f,e]) =
    case f of 
      (Var ide)                    -> text (pprint ide) <+> pp e
      (K App 2 [Var (Ide "+"),p])  -> pp p <+> text "+" <+> pp e
      (K App 2 [Var (Ide "-"),p])  -> pp p <+> text "-" <+> pp e
      (K App 2 [Var (Ide "*"),p])  -> pp p <+> text "*" <+> pp e
      (K App 2 [Var (Ide "/"),p])  -> pp p <+> text "/" <+> pp e
      (K App 2 [Var (Ide "=="),p]) -> pp p <+> text "==" <+> pp e
      _                            -> parens (pp f) <+> pp e

pp (K Abs 2 [t1,t2]) = (char '\\') <+> pp t1 <> (char '.') <+> pp t2

pp (K IfThenElse 3 [c,t1,t2]) = text "if" <+> pp c <+>
                                text "then" <+> pp t1
                                $$ text "else" <+> pp t2

pp (K Fix 1 [e]) = text "fix" <+> parens (pp e)

pp (MTerm id) = text id

pp _ = empty