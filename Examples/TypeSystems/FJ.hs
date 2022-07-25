----------------------------------------------------------------------
-- |
-- Module      :  Examples.TypeSystems.FJ
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Typing rules for FeatherweightJava
----------------------------------------------------------------------
module Examples.TypeSystems.FJ ( -- * FeatherweightJava typing rules
                                 var
                               , field
                               , invoke
                               , new
                               , cast
                               , method
                               , constructor
                               , fjclass
                               ) where


import TypeCheckLib.Syntax hiding (lkup)
import TypeCheckLib.TypeChecker hiding (union)

import Examples.Parser.FJ as FJ hiding (constructor)
import Examples.Printer.FJ

import Data.List (find, lookup, elem)
import Data.Tuple (swap)
import Data.Maybe (isNothing, fromJust, mapMaybe)
import Data.Foldable (toList)
import Data.Functor (fmap)
import qualified Data.Set


-- ###################################################################
--    Common expression, contexts and types used in inference rules
-- ###################################################################

------ Contexts -----|--- Identifier ---|- Methods/Constr.-|
ctx = MCtx "Gamma"   ;   m = MIde "m"   ;   m_j = MM "M"   ;
                                            k   = MC "K"   ;

------------------ Variables ------------------|-- Expressions ---|
this = Var (Ide "this") ; f   = Var (MIde "f") ; e   = MExpr "e"  ;
x    = Var (MIde "x")   ; f_i = Var (MIde "f") ; e0  = MExpr "e0" ;
x_i  = Var (MIde "x")   ; f_j = Var (MIde "f") ; e_i = MExpr "e"  ;
x_j  = Var (MIde "x")   ; f_k = Var (MIde "f")
x_k  = Var (MIde "x")

------------------------ Types -------------------------|
c   = MT "C"    ;   d   = MT "D"    ;   c'  = MT "C'"   ;
c0  = MT "C0"   ;   d0  = MT "D0"   ;   ec  = MT "E"    ;
c_i = MT "C"    ;   d_i = MT "D"    ;   e0C = MT "E0"   ;
c_j = MT "C"    ;   d_j = MT "D"    ;   t   = MT "T"    ;
c_k = MT "C"    ;   d_k = MT "D"    ;
      


-- ###################################################################
--                            Typing rules
-- ###################################################################

-- Typing rule for variable lookup:
--           T = Γ(x)
--         ----------- (Var)
--          Γ ⊢ x : T
var :: Rule
var = Rule [ t =:= (ctx ! x) <|> err ]
           ( ctx ⊢ x <:> t )
    where
      err = varError ctx x t



-- Typing rule for field access:
--      Γ ⊢ e : D     C = ftype(f,D)
--     -------------------------------- (Field)
--                Γ ⊢ e.f : C
field :: [FJClass] -> Rule
field prog = Rule [ ctx ⊢ e <:> d,
                    c =:= (mFtype prog f d) <|> err ]
                  ( ctx ⊢ (Invoke e f) <:> c )
    where
      err = fieldError prog (Invoke e f) f c d



-- Typing rule for method invocation:
--           Γ ⊢ e : E              Λ ( Γ ⊢ e_i : C_i)
--   mtype(m,E) = Λ (D_i) -> D    Λ (C_i <: D_i)     C = D
--  --------------------------------------------------------- (Invoke)
--                     Γ ⊢ e.m (Λ e_i) : C
invoke :: [FJClass] -> Rule
invoke prog =
    Rule [ ctx ⊢ e <:> ec,
           mSeq "I" (ctx ⊢ e_i <:> c_i),
           (mMtype prog m ec) =:= (mSeq "I" d_i ->: d) <|> err1,
           mSeq "I" ((prog ==> c_i <: d_i) <|> err2) ,
           c =:= d <|> err3 ]
          ( ctx ⊢ Invoke e mcall <:> c )
        where
          mcall = Meth m (mseq "I" e_i)
          err1  = mkErr "Wrong number of arguments in method call."
          err2  = mkErr "Wrong argument types in method call."
          err3  = typeMissmatch (Invoke e mcall) c d



-- Typing rule for constructor calls:
--        Λ (Γ ⊢ e_i : C_i)      fields(C) = U {D_i f_i}
--        Λ (C_i <: D_i)         D = C
--      -------------------------------------------------- (New)
--                     Γ ⊢ new C (Λ e_i) : D
new :: [FJClass] -> Rule
new prog = Rule [ mSeq "I" (ctx ⊢ e_i <:> c_i),
                  mFields prog c =:= (mset "I" (d_i, f_i)) <|> err1,
                  mSeq "I" ((prog ==> c_i <: d_i) <|> err2),
                  d =:= c <|> err3 ]
                ( ctx ⊢ New c (mseq "I" e_i) <:> d )
    where
      err1 = mkErr "Wrong constructor call."
      err2 = mkErr "Wrong argument types in constructor call."
      err3 = typeMissmatch (New c (mseq "I" e_i)) d c



-- Typing rule for up- and downcasts:
--             Γ ⊢ e : D           E = C
--      D <: C (upcast) or C <: D and C ≠ D (downcast)
--    --------------------------------------------------- (Cast)
--                      Γ ⊢ (C) e : E
cast :: [FJClass] -> Rule
cast prog = Rule [ ctx ⊢ e <:> d ,
                   upcast ∨ downcast <|> mkErr "Cast failed.",
                   ec =:= c <|> typeMissmatch (Cast c e) ec c]
                 ( ctx ⊢ Cast c e <:> ec )
    where
      upcast   = prog ==> d <: c
      downcast = (prog ==> c <: d) ∧ (c =/= d)



-- Typing rule for method definitions:
--    C' = OK in C     Λ (x_i:C_i),this : C ⊢ e0 : E0
--    E0 <: C0         superClass(C) = D
--    if mtype(m,D) = Λ (D_i) -> D0
--    then Λ (C_i = D_i) and C0 = D0
--   ---------------------------------------------------- (Method)
--         Γ ⊢ C0 m (Λ C_i x_i) { return e0; } : C'
method :: [FJClass] -> Rule
method prog =
    Rule [ c' =:= OkIn c <|> mkErr "Unification error.",
           ctx' ⊢ e0 <:> e0C ,
           (prog ==> e0C <: c0) <|>
           mkErr "Wrong return type in method body.",
           mSuperClass prog c =:= d <|>
           mkErr "Superclass lookup failed.",
           override <?> (subtypes ∧ (c0 =:= d0)) <|>
           mkErr "Wrong ovverride." ]
          ( ctx ⊢ M c0 m params (Return e0) <:> c' )
    where
      params   = mseq "I" (c_i,x_i)
      ctx'     = mInsertCtx this c (mCtxFromSeq params)
      override = (mMtype prog m d) =:= (mSeq "I" d ->: d0)
      subtypes = mSeq "I" (prog ==> c_i <: d_i)




-- Typing rule for constructor definitions:
--   superClass(C) = D      fields(C) = U {C_i x_i}
--   fields(D) = U {D_j x_j}       T = Ok in C
--        fields(C) \ fields(D) = U {E_k f_k}
--   -------------------------------------------------- (Constructor)
--     Γ ⊢ C (Λ C_i x_i) { super(Λ x_j);
--                          Λ(this.f_k = f_k;) } : T
constructor :: [FJClass] -> Rule
constructor prog =
    Rule [ (mSuperClass prog c) =:= d <|>
           mkErr "Superclass lookup failed.",
           (mFields prog c) =:= (mset "I" (c_i,x_i)) <|>
           mkErr "Wrong number of parameters in constructor definition.",
           (mFields prog d) =:= (mset "J" (d_j,x_j)) <|>
           mkErr "Wrong number of arguments in super constructor call.",
           flds =:= (mset "K" (e_k,f_k)) <|>
           mkErr "Wrong number of assignments in constructor body.",
           t =:= OkIn c <|> mkErr "Type Missmatch." ]
          ( ctx ⊢ (FJ.C c ps s as) <:> t )
    where
      ps   = mseq "I" (c_i,x_i)
      s    = Meth (Ide "super") (mseq "J" x_j)
      as   = mseq "K" (Assign (Invoke this f_k) f_k)
      e_k  = MT "E"
      flds = mFields prog c \\ mFields prog d



-- Typing rule for class definitions:
--   Γ ⊢ K : Ok in C     Λ (Γ ⊢ M_j : Ok in C)     T = Ok
-- --------------------------------------------------------- (Class)
--  Γ ⊢ class C extends D { (Λ C_i f_i;)  K  (Λ M_j) } : T
fjclass :: [FJClass] -> Rule
fjclass prog = Rule [ ctx ⊢ k <:> okInC ,
                      mSeq "J" (ctx ⊢ m_j <:> okInC) ,
                      t =:= mkT "Ok" <|> mkErr "Type missmatch." ]
                    ( ctx ⊢ (Class c d as k ms) <:> t )
    where
      as    = mseq "I" (c_i,f_i)
      ms    = mseq "J" m_j
      okInC = OkIn c



-- ###################################################################
-- Auxiliary functions used in the Featherweight Java deduction rules
-- ###################################################################


-- | Type lookup of a class field.
ftype :: [FJClass] -> FJExpr -> Ty -> Maybe Ty
ftype _ _ (TV _)             = Nothing
ftype _ _ (T (Ide "Object")) = Nothing
ftype prog f c = if isNothing cls then Nothing
                 else ty
    where
      cls          = find (\ cl -> clName cl == c) prog
      (ObjSeq as)  = attributes (fromJust cls)
      ty           = lookup f (map swap (toList as))



-- | Meta level version of ftype.
mFtype :: [FJClass] -> FJExpr -> Ty -> Ty
mFtype prog f c = TyFun (MF "ftype" (uncurry3 ftype) (prog,f,c))



-- | Interactive test function for ftype.
testFType f c fileName = do ast <- parseFromFile fileName
                            putStrLn (pprint (ftype ast f c))


----------------------------------------------------------------------

-- | Type lookup of a class method.
mtype :: [FJClass] -> Ide -> Ty -> Maybe Ty
mtype _ _ (TV _)             = Nothing
mtype _ _ (T (Ide "Object")) = Just Bottom
mtype prog m c = if isNothing cls then Just Bottom
                 else ty
    where
      cls         = find (\ cl -> clName cl == c) prog
      (ObjSeq ms) = methods (fromJust cls)
      mth         = find (\ mth -> mName mth == m) (toList ms)
      ty          = maybe (Just Bottom) (Just . mkMT) mth

-- | Build method type for a given method definition.
mkMT :: FJMethod -> Ty
mkMT (M rt _ (ObjSeq ps) _) = (extractTSeq ps) ->: rt
    where
      extractTSeq = (TySeq . ObjSeq) . (fmap fst)
      


-- | Meta level version of mtype.
mMtype :: [FJClass] -> Ide -> Ty -> Ty
mMtype prog m c = TyFun (MF "mtype" (uncurry3 mtype) (prog,m,c))


-- | Interactive test function for mtype.
testMType m c fileName = do ast <- parseFromFile fileName
                            putStrLn (pprint (mtype ast m c))


----------------------------------------------------------------------

-- | Fields of a given class.
fields :: [FJClass] -> Ty -> Maybe (Set (Ty,FJExpr))
fields _  (TV _)             = Nothing
fields [] (T (Ide "Object")) = Just (ObjSet (Data.Set.empty))
fields [] _                  = Nothing
-- TODO: improve implementation of fields
fields prog c = Just (foldl (\ s1 s2 -> fromJust (union s1 s2))
                            emptySet
                            (mapMaybe (flds prog)
                                      (c:(superClasses prog c)))
                     )
    where
      flds _ (T (Ide "Object")) = Just (ObjSet (Data.Set.empty))
      flds [] c       = Just (ObjSet (Data.Set.empty))
      flds (cl:cls) c = if clName cl == c
                        then Just (setFromSeq (attributes cl))
                        else flds cls c 


-- | Meta level version of fields.
mFields :: [FJClass] -> Ty -> Set (Ty,FJExpr)
mFields prog c = SetFun (MF "fields" (uncurry fields) (prog,c))


-- | Interactive test function for fields.
testFields c fileName = do ast <- parseFromFile fileName
                           putStrLn (pprint (fields ast c))


----------------------------------------------------------------------

-- | Superclass of a given class.
superCls :: [FJClass] -> Ty -> Maybe Ty
superCls _ (TV _)             = Nothing
superCls _ (T (Ide "Object")) = Just Bottom
superCls [] _                 = Just Bottom
superCls (c:cls) cl = if clName c == cl then Just (superClass c)
                      else superCls cls cl


-- | Meta level version of superCls.
mSuperClass :: [FJClass] -> Ty -> Ty
mSuperClass prog c = TyFun (MF "superClass" (uncurry superCls) (prog,c))


-- | Interactive test function for superCls.
testSuperClass c fileName = do ast <- parseFromFile fileName
                               putStrLn (pprint (superCls ast c))


----------------------------------------------------------------------

-- | Simple, single inheritance subtype solver:
-- * C <: C
-- * C <: D if CT(C) = class C extends D {...}
-- * C <: E if there exists a type D, such that C <: D and D <: E
subtype :: [FJClass] -> Ty -> Ty -> Maybe Bool
subtype _ (TV _) _ = Nothing
subtype _ _ (TV _) = Nothing
subtype _ Bottom _ = Just False
subtype _ _ Bottom = Just False
subtype prog c d | c == d    = Just True
                 | otherwise = Just (d `elem` superClasses prog c)


-- | All super classes of a given class.
-- Note: This function requires object level arguments.
superClasses :: [FJClass] -> Ty -> [Ty]
superClasses _ (T (Ide "Object")) = []
superClasses prog c = case superCls prog c of
                        Just d  -> d : (superClasses prog d)
                        Nothing -> error "Wrong usage of 'superClasses'."


-- | Interactive test function for subtype.
testSubType c d fileName = do ast <- parseFromFile fileName
                              putStrLn (show (subtype ast c d))




-- | Operator-based meta level version of subtype.
(==>) :: [FJClass] -> (Ty, Ty) -> Constraint Ty
prog ==> (s,t) = Predicate (MF "<:" (uncurry (subtype prog)) (s,t))
                 (mkErr "Error: could not solve subtype constraint.")

s <: t = (s,t)

infix 6 <:
infix 5 ==>


-- ###################################################################
--              Meta level versions of auxiliary functions
-- ###################################################################

mCtxFromSeq :: Sequence (Ty,FJExpr) -> Context
mCtxFromSeq s = CtxFun (MF "ctxFromSeq" ctxFromSeq s)
    where
      ctxFromSeq (MetaSeq _ _) = Nothing
      ctxFromSeq (ObjSeq s)    = fromSeq (ObjSeq (fmap swap s))



-- ###################################################################
--                            Error Messages
-- ###################################################################

varError :: Context -> FJExpr -> Ty -> ErrorMsg
varError ctx x ty = ErrorMsg x (MF "" (Just . msg) (ctx,x,ty))
    where
      msg :: (Context, FJExpr, Ty) -> String
      msg (ctx,x,ty) =
          case ((lkup x ctx) :: Maybe Ty) of
            Nothing  -> "Undefined variable: " ++ pprint x
            Just ty' -> "Type Missmatch: " ++
                        "Could not match expected type `" ++ pprint ty
                        ++ "' against inferred type `" ++ pprint ty'
                        ++ "'"


fieldError :: [FJClass] -> FJExpr -> FJExpr -> Ty -> Ty -> ErrorMsg
fieldError p exp f c d = ErrorMsg exp (MF "" (Just . msg) (p,f,c,d))
    where
      msg :: ([FJClass],FJExpr,Ty,Ty) -> String
      msg (p,f,c,d) =
          case (ftype p f d) of
            Nothing -> pprint f ++ " is not a field of class " ++
                           pprint d
            Just c' -> "Type Missmatch: " ++
                       "Could not match expected type `" ++ pprint c
                       ++ "' against inferred type `" ++ pprint c'
                       ++ "'"


typeMissmatch :: FJExpr -> Ty -> Ty -> ErrorMsg
typeMissmatch expr t1 t2 = ErrorMsg expr (MF "" (Just . msg) (t1,t2))
    where
      msg :: (Ty,Ty) -> String
      msg (t1,t2) = "Type Missmatch: Could not match expected type `"
                    ++ pprint t1 ++ "' against inferred type `" ++
                    pprint c' ++ "'"