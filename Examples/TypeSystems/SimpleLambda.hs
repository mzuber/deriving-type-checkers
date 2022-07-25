----------------------------------------------------------------------
-- |
-- Module      :  Examples.TypeSystems.SimpleLambda
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Typing rules for a simply typed lambda calculus.
----------------------------------------------------------------------
module Examples.TypeSystems.SimpleLambda ( var,
                                           abs,
                                           app ) where

import TypeCheckLib.Syntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.TypeChecker

import Examples.Printer.MiniML

import Prelude hiding (abs)


-- ###################################################################
--    Common expression, contexts and types used in inference rules
-- ###################################################################

ctx = MCtx "Gamma"
x   = MIde "x"
e   = MTerm "e"
f   = MTerm "f"
t   = MT "T"
t1  = MT "T1"
t2  = MT "T2"
err = mkErr "Error"


-- ###################################################################
--                          Typing rules
-- ###################################################################

-- Typing rule for variable lookup:
--           T = Γ(x)
--         ----------- (Var)
--          Γ ⊢ x : T
var :: Rule
var = Rule [t =:= (ctx ! Var x) <|> err]
           (ctx ⊢ Var x <:> t)

        
 
-- Typing rule for lambda abstraction:
--        Γ,x:T1 ⊢ e : T2       T = T1 -> T2
--       ------------------------------------ (Abs)
--                  Γ ⊢ λ x.e : T
abs :: Rule
abs = Rule [ctx' ⊢ e <:> t2 , t =:= (t1 ->: t2) <|> err]
           (ctx ⊢ exp <:> t)
      where
        exp  = K Abs 2 [Var x, e]
        ctx' = mInsertCtx (Var x) t1 ctx
        err  = tyMM t (t1 ->: t2) exp


-- Typing rule for application.
--      Γ ⊢ f : T1     Γ ⊢ e : T2     T1 = T2 -> T
--     -------------------------------------------- (App)
--                    Γ ⊢ (f) e : T
app :: Rule
app = Rule [ ctx ⊢ f <:> t1 , ctx ⊢ e <:> t2,
             t1 =:= (t2 ->: t) <|> err ]
           ( ctx ⊢ (K App 2 [f,e]) <:> t )



-- ##################################################################
--                          Error Messages
-- ##################################################################

-- Type missmatch.
tyMM :: Ty -> Ty -> Term -> ErrorMsg
tyMM t1 t2 e = ErrorMsg e (MF "type missmatch" (uncurry msg) (t1,t2))
    where
      msg :: Ty -> Ty -> Maybe String
      msg (MT _) _ = Nothing
      msg _ (MT _) = Nothing
      msg t1 t2 = Just ("Couldn't match expected type `" ++ pprint t1 ++
                        "' against inferred type `" ++ pprint t2 ++ "'")