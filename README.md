Deriving Type Checkers
======================

Abstract
--------

The relationship between a type system's specification and the implementation of the type checker is a recurring issue
when writing compilers for programming languages and it is an ongoing question if - and if so, how - the formal description
of a type system can be used to support the compiler writer when implementing the type checking phase. In this paper we
propose type systems formalized by constraint-based inference rules to form an ideal abstraction to accomplish the task
of automatically deriving type checking functionality from them. We develop a set of algorithms employing the constraint-
based flavor of the rules to perform type checks and present the design and implementation of a Haskell library utilizing
these algorithms to provide functionality for the type checking phase based on the chosen abstraction.

Citation
--------

Martin Zuber and Fabian Linges. Deriving Type Checkers. In _Technical Report 2012–09_, TU Berlin, 2012.

```bibtex
@techreport{zuber2012,
    title = {Deriving Type Checkers},
    author = {Zuber, Martin and Linges, Fabian},
    year = {2012},
    number = {2012-09},
    issn = {1436-9915},
    institution = {TU Berlin},
    url = {https://github.com/mzuber/deriving-type-checkers/releases/download/v0.3.0/TR_2012-09_Deriving_Type_Checkers.pdf}
}
```

Example
-------

Typing rules for a simply typed lambda calculus.

```haskell
import TypeCheckLib.Syntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.TypeChecker

-- Common expression, contexts and types used in inference rules
ctx = MCtx "Gamma"
x   = MIde "x"
e   = MTerm "e"
f   = MTerm "f"
t   = MT "T"
t1  = MT "T1"
t2  = MT "T2"
err = mkErr "Error"

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

-- Error message for type mismatch.
tyMM :: Ty -> Ty -> Term -> ErrorMsg
tyMM t1 t2 e = ErrorMsg e (MF "type mismatch" (uncurry msg) (t1,t2))
    where
      msg :: Ty -> Ty -> Maybe String
      msg (MT _) _ = Nothing
      msg _ (MT _) = Nothing
      msg t1 t2 = Just ("Couldn't match expected type `" ++ pprint t1 ++
                        "' against inferred type `" ++ pprint t2 ++ "'")
```

Type checker for simply typed lambda calculus.

```haskell
-- | Simple lambda typing rules.
simpleLambdaRules :: [Rule]
simpleLambdaRules = [var, abs, app]

-- | Compute type of simple lambda expression.
computeType :: Term -> TypeCheckResult
computeType exp = computeTy defaultMode simpleLambdaRules exp

-- | Check type of simple lambda expression.
checkType :: Term -> Ty -> TypeCheckResult
checkType exp ty = checkTy defaultMode simpleLambdaRules exp ty


-- | Infer the type of a simple lambda expression.
inferType :: String -> IO ()
inferType exp = let res = computeType (parse exp)
                in case res of
                     Success ty  -> putStrLn (pprint ty)
                     Failure msg -> putStrLn msg
                     Error msg   -> putStrLn msg
```
