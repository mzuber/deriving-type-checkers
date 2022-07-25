----------------------------------------------------------------------
-- |
-- Module      :  Examples.TypeSystems.MiniML
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Typing rules for Mini-ML.
----------------------------------------------------------------------
module Examples.TypeSystems.MiniML ( -- * Simple Lambda
                                     varpoly,
                                     abs,
                                     app,
                                     -- * Base types
                                     true,
                                     false,
                                     const,
                                     add,
                                     sub,
                                     mul,
                                     div,
                                     eqi,
                                     and,
                                     or,
                                     -- * Extensions
                                     cond,
                                     pair,
                                     letpoly,
                                     letrec,
                                     fix,
                                     -- * Auxiliary functions
                                     gen ) where

import TypeCheckLib.Syntax hiding ((>=))
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.TypeChecker hiding (gen, and, or)
import qualified TypeCheckLib.Rule as Rule (gen)

import Examples.TypeSystems.SimpleLambda
import Examples.TypeSystems.LambdaBaseTypes
import Examples.TypeSystems.LambdaExtensions
import Examples.Printer.MiniML

import Prelude hiding (lookup, abs, div, and, or, const, (>=))
import qualified Data.Set as S


-- ###################################################################
--    Common expression, contexts and types used in inference rules
-- ###################################################################

ctx = MCtx "Gamma"
x   = MIde "x"
e1  = MTerm "e1"
e2  = MTerm "e2"
t   = MT "T"
t1  = MT "T1"
t2  = MT "T2"
t3  = MT "T3"
err = mkErr "Error"


-- ###################################################################
--                            Typing rules
-- ###################################################################

-- Typing rule for polymorphic lets:
--  Γ ⊢ e1 : T1     T2 = gen(Γ,T1)   Γ,x:T2 ⊢ e2 : T3   T = T3
-- ------------------------------------------------------------- (Let)
--                    Γ ⊢ let x = e1 in e2 : T
letpoly :: Rule
letpoly = Rule [ ctx ⊢ e1 <:> t1
               , t2 =:= gen ctx t1 <|> err
               , ctx' ⊢ e2 <:> t3
               , t =:= t3 <|> err ]
               ( ctx ⊢ (K Let 3 [Var x,e1,e2]) <:> t )
    where
      ctx' = mInsertCtx (Var x) t2 ctx


-- Typing rule for polymorphic variable lookup:
--      T1 = Γ(x)     T1 >= T
--     ----------------------- (Var)
--            Γ ⊢ x : T
varpoly :: Rule
varpoly = Rule [ t1 =:= (ctx ! Var x) <|> err,
                 (t1 >= t) <|> err ]
               ( ctx ⊢ Var x <:> t )



-- ###################################################################
--           Meta level definitions for auxiliary functions
-- ###################################################################

gen ctx ty = TyFun (MF "gen" (uncurry Rule.gen) (ctx,ty))

(>=) :: Ty -> Ty -> Constraint Ty
t1 >= t2 = Constraint (MF ">=" (uncurry genInstOf) (t2,t1))
                      (mkErr "Generic instance check failed.")