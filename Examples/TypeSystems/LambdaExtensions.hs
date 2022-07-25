----------------------------------------------------------------------
-- |
-- Module      :  Examples.TypeSystems.LambdaExtensions
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Typing rules for conditionals, pairs and recursive, monomorphic
-- lets.
----------------------------------------------------------------------
module Examples.TypeSystems.LambdaExtensions ( cond,
                                               pair,
                                               letmono,
                                               letrec,
                                               fix ) where

import TypeCheckLib.Syntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.TypeChecker

import Examples.Printer.MiniML


-- ###################################################################
--   Common expression, contexts and types used in inference rules
-- ###################################################################

ctx = MCtx "Gamma"

x   = MIde "x"
e1  = MTerm "e1"
e2  = MTerm "e2"
e3  = MTerm "e3"
f   = MTerm "f"

t    = MT "T"
t1   = MT "T1"
t2   = MT "T2"
t3   = MT "T3"
bool = mkT "bool"

err = mkErr "Error"


-- ###################################################################
--                           Typing rules
-- ###################################################################

-- Typing rule for conditionals:
--    Γ ⊢ e1 : T1    Γ ⊢ e2 : T2    Γ ⊢ e3 : T3
--     T1 = bool       T = T2          T = T3
--   -------------------------------------------- (If)
--           Γ ⊢ if e1 then e2 else e3 : T  
cond :: Rule
cond = Rule [ctx ⊢ e1 <:> t1, ctx ⊢ e2 <:> t2, ctx ⊢ e3 <:> t3,
             t1 =:= bool <|> err, t =:= t2 <|> err, t =:= t3 <|> err]
            (ctx ⊢ (K IfThenElse 3 [e1,e2,e3]) <:> t)


-- Typing rule for pairs:
--     Γ ⊢ e1 : T1     Γ ⊢ e2 : T2     T = T1 x T2
--    --------------------------------------------- (Pair)
--                  Γ ⊢ (e1,e2) : T
pair :: Rule
pair = Rule [ ctx ⊢ e1 <:> t1 , ctx ⊢ e2 <:> t2,
              t =:= (t1 × t2) <|> err ]
            ( ctx ⊢ (K Tuple 2 [e1,e2]) <:> t )


-- Typing rule for monomorphic let expressions:
--     Γ ⊢ e1 : T1     Γ,x:T1 ⊢ e2 : T2     T = T2
--    --------------------------------------------- (Let)
--             Γ ⊢ let x = e1 in e2 : T
letmono :: Rule
letmono = Rule [ ctx ⊢ e1 <:> t1, ctx' ⊢ e2 <:> t2,
                 t =:= t2 <|> err ]
               ( ctx ⊢ (K Let 3 [Var x,e1,e2]) <:> t )
          where
            ctx' = mInsertCtx (Var x) t1 ctx


-- Typing rule for recursive let expressions:
--      Γ ⊢ let x = fix (λ x.e1) in e2 : T2     T = T2
--     ------------------------------------------------ (LetRec)
--               Γ ⊢ letrec x = e1 in e2 : T
letrec :: Rule
letrec = Rule [ ctx ⊢ (K Let 3 [Var x, fix, e2]) <:> t2,
                t =:= t2 <|> err ]
              ( ctx ⊢ (K LetRec 3 [Var x, e1, e2]) <:> t )
         where
           fix = K Fix 1 [K Abs 2 [Var x, e1]]


-- Typing rule for the fixpoint function:
--        Γ ⊢ f : T1      T1 = T -> T
--       ------------------------------ (Fix)
--               Γ ⊢ fix f : T
fix :: Rule
fix = Rule [ctx ⊢ f <:> t1 , t1 =:= (t ->: t) <|> err]
           (ctx ⊢ (K Fix 1 [f]) <:> t)