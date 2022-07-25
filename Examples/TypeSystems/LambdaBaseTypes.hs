----------------------------------------------------------------------
-- |
-- Module      :  Examples.TypeSystems.LambdaBaseTypes
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Typing rules for the base types @int@ and @bool@.
----------------------------------------------------------------------
module Examples.TypeSystems.LambdaBaseTypes ( true,
                                              false,
                                              const,
                                              add,
                                              sub,
                                              mul,
                                              div,
                                              eqi,
                                              and,
                                              or ) where

import TypeCheckLib.Syntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.TypeChecker hiding (and, or)

import Examples.Printer.MiniML

import Prelude hiding (const, div, and, or)


-- ###################################################################
--    Common expression, contexts and types used in inference rules
-- ###################################################################

ctx  = MCtx "Gamma"
t    = MT "T"
bool = mkT "bool"
int  = mkT "int"
n    = MConst "n"
err  = mkErr "Error"


-- ###################################################################
--                           Typing rules
-- ###################################################################

-- Typing rule for the boolean value true:
--               T = bool
--            -------------- (True)
--             Γ ⊢ true : T
true :: Rule
true = Rule [t =:= bool <|> err]
            (ctx ⊢ Var (Ide "true") <:> t)
         
         
-- Typing rule for the boolean value false:
--               T = bool
--           --------------- (False)
--            Γ ⊢ false : T
false :: Rule
false = Rule [t =:= bool <|> err]
             (ctx ⊢ Var (Ide "false") <:> t)


-- Typing rule for integer values:
--              T = int
--            ----------- (Int)
--             Γ ⊢ n : T
const :: Rule
const = Rule [t =:= int <|> err]
             (ctx ⊢ n <:> t)


-- Typing rule for addition of integer values:
--          T = int -> (int -> int)
--          ----------------------- (Add)
--                Γ ⊢ + : T
add :: Rule
add = Rule [t =:= (int ->: (int ->: int)) <|> err]
           (ctx ⊢ Var (Ide "+") <:> t)


-- Typing rule for substraction of integer values:
--          T = int -> (int -> int)
--          ----------------------- (Sub)
--                Γ ⊢ - : T
sub :: Rule
sub = Rule [t =:= (int ->: (int ->: int)) <|> err]
           (ctx ⊢ Var (Ide "-") <:> t)


-- Typing rule for multiplication of integer values:
--          T = int -> (int -> int)
--          ----------------------- (Mul)
--                Γ ⊢ * : T
mul :: Rule
mul = Rule [t =:= (int ->: (int ->: int)) <|> err]
           (ctx ⊢ Var (Ide "*") <:> t)


-- Typing rule for dividing integer values:
--          T = int -> (int -> int)
--          ----------------------- (Div)
--                Γ ⊢ / : T
div :: Rule
div = Rule [t =:= (int ->: (int ->: int)) <|> err]
           (ctx ⊢ Var (Ide "/") <:> t)


-- Typing rule for comparision of integer values:
--          T = int -> (int -> bool)
--          ------------------------ (Eqi)
--                Γ ⊢ == : T
eqi :: Rule
eqi = Rule [t =:= (int ->: (int ->: bool)) <|> err]
           (ctx ⊢ Var (Ide "==") <:> t)


-- Typing rule for the conjunction of booleans:
--          T = bool -> (bool -> bool)
--          -------------------------- (And)
--                 Γ ⊢ and : T
and :: Rule
and = Rule [t =:= (bool ->: (bool ->: bool)) <|> err]
           (ctx ⊢ Var (Ide "and") <:> t)


-- Typing rule for the disjunction of booleans:
--          T = bool -> (bool -> bool)
--          -------------------------- (Or)
--                 Γ ⊢ or : T
or :: Rule
or = Rule [t =:= (bool ->: (bool ->: bool)) <|> err]
          (ctx ⊢ Var (Ide "or") <:> t)