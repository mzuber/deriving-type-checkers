{-# LANGUAGE FlexibleInstances, DeriveDataTypeable, GADTs,
             ScopedTypeVariables #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Rule
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Module providing the library's data structures to encode
-- constraint-based deduction rules.
----------------------------------------------------------------------
module TypeCheckLib.Rule ( -- * Rules
                           Rule (..)
                           -- * Judgements
                         , Judgement (..)
                           -- Auxiliary functions for judgements
                         , isC
                         , isJ
                         , asList
                           -- * Contexts
                         , Context (..)
                         , Ctx.empty
                         , Ctx.insert
                         , Ctx.singleton
                         , Ctx.fromList
                         , Ctx.fromSeq
                         , Ctx.delete
                         , Ctx.lkup
                         , Ctx.union
                         , mInsertCtx
                         , mDeleteCtx
                         , (!)
                         , gen
                           -- * Constraints
                         , Constraint (..)
                           -- ** Error messages for constraints
                         , ErrorMsg (..)
                         , mkErr
                         , mkMsg
                           -- ** Auxiliary functions for constraints
                         , isEq
                         , isP
                         , isUC
                         , err
                         , replaceErr
                            -- * PrettyPrinter
                         , pprint
                         ) where


import TypeCheckLib.AbstractSyntax
import TypeCheckLib.Context as Ctx
import TypeCheckLib.Type
import TypeCheckLib.Substitution as S
import TypeCheckLib.Unification
import TypeCheckLib.Instantiation
import TypeCheckLib.Evaluable
import TypeCheckLib.Vars

import Prelude hiding (lookup, foldr)
import Data.Maybe (fromMaybe, fromJust, isJust)
import Data.List (intercalate)
import Data.Set (unions, difference)
import Data.Tuple (swap)
import Data.Typeable
import Data.Foldable
import Data.Functor (fmap)


-- ###################################################################
--                      Rules and judgements
-- ###################################################################

-- | A deduction rule consists of a list of premises P1 ... Pn and a
-- conclusion C, such that the conclusion holds under the given
-- premises. The conclusion C is a typing judgement over terms,
-- definitions or containers; the premises range over typing
-- judgements and constraints.
data Rule = Rule [Judgement] Judgement
            deriving (Show, Eq, Ord, Typeable)


-- | Judgements of a deduction rule range over Hindley/Milner type
-- judgements (a ternary relation between a context, an expression and
-- a type), constraints, and (meta level) sequences of
-- judgements. Additionally, this data structure provides a special
-- error case signalizing that no matching rule was found during
-- constraint generation and a seperator containing an id for the
-- instantiated rule (this is used for debugging and testing).
data Judgement where
    -- Typing judgement
    J :: (Show a, Ord a, PrettyPrint a, Typeable a, AST a, Vars a,
          Evaluable a, Substitutable a, Unifiable a, Instantiable a) =>
         Context -> a -> Ty -> Judgement
    -- Constraint
    C :: (Show a, Ord a, PrettyPrint a, Typeable a, AST a, Vars a,
          Evaluable a, Substitutable a, Unifiable a, Instantiable a) =>
         (Constraint a) -> Judgement
    -- Judgement sequence
    JSeq   :: (Sequence Judgement) -> Judgement
    -- Error case
    NoRule :: Judgement -> Judgement
    -- Separator
    Sep    :: Int -> Judgement
    deriving Typeable


instance Show Judgement where
    show (J ctx exp ty) = show ctx ++ " |- " ++
                          show exp ++ " : " ++ show ty
    show (C c)          = "C (" ++ show c ++ ")"
    show (JSeq s)       = "JSeq (" ++ show s ++ ")"
    show (NoRule j)     = "NoRule (" ++ show j ++ ")"
    show (Sep n)        = "Sep (" ++ show n ++ ")"


instance Eq Judgement where
    (J c1 (e1 :: a) t1) == (J c2 e2 t2) =
        let c = c1 == c2
        in case (cast e2) :: Maybe a of
             Nothing  -> False
             Just e2' -> c && (e1 == e2') && (t1 == t2)
    (C (c1 :: (Constraint a))) == (C c2) =
        case (cast c2) :: Maybe (Constraint a) of
          Nothing  -> False
          Just c2' -> c1 == c2'
    (JSeq s1)   == (JSeq s2)   = s1 == s2
    (NoRule j1) == (NoRule j2) = j1 == j2
    (Sep n1)    == (Sep n2)    = n1 == n2
    _           == _           = False


instance Ord Judgement where
    (J c1 (e1 :: a) t1) < (J c2 e2 t2) =
        let c = c1 < c2
        in case (cast e2) :: Maybe a of
             Nothing  -> False
             Just e2' -> c && (e1 < e2') && (t1 < t2)
    (C (c1 :: (Constraint a))) < (C c2) =
        case (cast c2) :: Maybe (Constraint a) of
          Nothing  -> False
          Just c2' -> c1 < c2'
    (JSeq s1)   < (JSeq s2)   = s1 < s2
    (NoRule j1) < (NoRule j2) = j1 < j2
    (Sep n1)    < (Sep n2)    = n1 < n2
    _           < _           = False


instance Evaluable Judgement where
    isEvaluable (J ctx exp ty) = isEvaluable ctx && isEvaluable exp
                                 && isEvaluable ty
    isEvaluable (C c)          = isEvaluable c
    isEvaluable (JSeq s)       = isEvaluable s
    isEvaluable _              = True

    eval (J ctx exp ty) = J (eval ctx) (eval exp) (eval ty)
    eval (C c)          = C (eval c)
    eval (JSeq s)       = JSeq (eval s)
    eval (NoRule j)     = NoRule (eval j)
    eval s@(Sep n)      = s

    isMF (J ctx exp ty) = isMF ctx || isMF exp || isMF ty
    isMF (C c)          = isMF c
    isMF (JSeq s)       = isMF s
    isMF _              = False


instance Substitutable Judgement where
    apply o (J ctx exp ty) = J (o .@. ctx) (o .@. exp) (o .@. ty)
    apply o (C c)          = C (o .@. c)
    apply o (JSeq s)       = JSeq (o .@. s)
    apply o (NoRule j)     = NoRule (o .@. j)
    apply _ s@(Sep _)      = s


instance Instantiable Judgement where
    unfold (J ctx exp ty) = J (unfold ctx) (unfold exp) (unfold ty)
    unfold (C c)          = C (unfold c)
    unfold (JSeq s)       = JSeq (unfold s)
    unfold (NoRule j)     = NoRule (unfold j)
    unfold s@(Sep _)      = s

    indexM (J ctx exp ty) n = J (indexM ctx n) (indexM exp n)
                                (indexM ty n)
    indexM (C c)          n = C (indexM c n)
    indexM (JSeq s)       n = JSeq (indexM s n)
    indexM (NoRule j)     n = NoRule (indexM j n)
    indexM s@(Sep _)      _ = s

    instMT (J ctx exp ty) = do o <- instMT ty
                               p <- instMT (o .@. exp)
                               return (o .*. p)
    instMT (C c)          = instMT c
    instMT j              = return S.empty


instance Vars Judgement where
    fv (J ctx exp ty) = unions [fv ctx, fv exp, fv ty]
    fv (C c)          = fv c
    fv (JSeq s)       = fv s
    fv _              = unions []

    bv (J ctx exp ty) = unions [bv ctx, bv exp, bv ty]
    bv (C c)          = bv c
    bv (JSeq s)       = bv s
    bv _              = unions []


-- | Discriminator for constraint-judgements.
isC :: Judgement -> Bool
isC (C _)      = True
isC (NoRule _) = True
isC _          = False


-- | Discriminator for judgements.
isJ (J _ _ _) = True
isJ _         = False


-- | 'asList' converts object level judgement
--   sequences to judgement lists.
asList :: Judgement -> [Judgement]
asList (JSeq (ObjSeq s)) = toList s
asList j                 = [j]



-- ###################################################################
--                            Contexts
-- ###################################################################

-- | Meta level version for 'insert' on contexts.
mInsertCtx :: ( Show a, AST a, PrettyPrint a, Evaluable a,
                Substitutable a, Instantiable a, Vars a ) =>
              a -> Ty -> Context -> Context
mInsertCtx e ty ctx = CtxFun (MF "insert" (uncurry3 Ctx.insert)
                                  (e,ty,ctx))


-- | Meta level version for 'delete' on contexts.
mDeleteCtx :: ( AST a, Instantiable a, Substitutable a,
                Evaluable a, Show a, PrettyPrint a, Vars a ) =>
              a -> Context -> Context
mDeleteCtx e ctx = CtxFun (MF "delete" (uncurry Ctx.delete) (e,ctx))


-- | Meta level version for 'lkup' on contexts.
(!) :: ( AST a, PrettyPrint a, Evaluable a,
         Substitutable a, Instantiable a, Vars a ) =>
       Context -> a -> Ty
ctx ! x = TyFun (MF "lookup" (uncurry Ctx.lkup) (x,ctx))


-- | Quantify free type variables of a type over a given context.
gen :: Context -> Ty -> Maybe Ty
gen (MCtx _) _ = Nothing
gen _ (MT _)   = Nothing
gen ctx ty  = let tvs  = fv ty `difference` fv ctx
                  tvs' = toList tvs
              in if null tvs' then Just ty
                 else Just (TS tvs' ty)



-- ###################################################################
--                           Error messages
-- ###################################################################

-- | An "ErrorMsg" wraps up the expression, for which a generated
-- constraint could not be solved as well as a function used to create
-- an according error message.
data ErrorMsg = forall a . (PrettyPrint a, Substitutable a,
                            Instantiable a) =>
                           ErrorMsg a (MetaFun String)
                           deriving Typeable


instance Show ErrorMsg where
    show (ErrorMsg a err) = "ErrorMsg (" ++ show a ++
                            ") (" ++ show err ++ ")"

instance Eq ErrorMsg where
    _ == _ = True

instance Ord ErrorMsg where
    _ < _ = True

instance Substitutable ErrorMsg where
    apply o (ErrorMsg a err) = ErrorMsg (apply o a) (apply o err)

instance Instantiable ErrorMsg where
    unfold (ErrorMsg a err)   = ErrorMsg (unfold a) (unfold err)
    indexM (ErrorMsg a err) n = ErrorMsg (indexM a n) (indexM err n)
    instMT                    = const (return S.empty)


-- | Create an 'ErrorMsg' just consisting of a 'String'.
mkErr :: String -> ErrorMsg
mkErr msg = ErrorMsg () (MF "" (const (Just msg)) ())

-- | Build the 'String' containing the actual error message by
-- evaluating the wrapped up function.
mkMsg :: ErrorMsg -> String
mkMsg (ErrorMsg a (MF _ f args))
    | isEvaluable args = fromJust (f (eval args))
    | otherwise        = "Constraint contains meta level elements."


-- ###################################################################
--                           Constraints
-- ###################################################################

type Unifier = (Bool, Substitution)

-- | Constraints over a certain domain @a@. The constraint domain
-- has to provide an instance for 'Eq' to be able to solve such
-- constraints by unification.
data Constraint a
    -- | Equality constraint
    = Eq a a ErrorMsg
    -- | User-defined Constraint
    | Constraint (MetaFun Unifier) ErrorMsg
    -- | n-ary predicate
    | Predicate (MetaFun Bool) ErrorMsg
    -- | Negated constraint
    | Not (Constraint a) ErrorMsg
    -- | Constraint conjunction
    | And (Constraint a) (Constraint a) ErrorMsg
    -- | Constraint disjunction
    | Or (Constraint a) (Constraint a) ErrorMsg
    -- | Conditional constraint
    | If (Constraint a) (Constraint a) ErrorMsg
    -- | Constraint sequence
    | ConstraintSeq (Sequence (Constraint a)) ErrorMsg
    deriving (Show, Eq, Ord, Typeable)


instance (Evaluable a, Eq a) => Evaluable (Constraint a) where
    -- Discriminator for constraints over object level elements.
    -- Note: this function will be used during constraint solving to
    -- determine, wether a constraint can be tried to be solved. Thus
    -- constraints ranging over several other constraints are treated
    -- a little different then expected. A 'compound' constraint
    -- (e.g. conjunctions or disjunctions) can be tried to be solved
    -- if at least one of the bound constraints is evaluable. The
    -- dissolving of conditional constraints can be started if the
    -- condition is evaluable. This behavior is chosen for the
    -- following reason: In a 'compound' constraint, the solution of
    -- one of the bound constraints can depend on the solution of
    -- another bound constraint, e.g. possible meta level elements in
    -- this constraint might only be instantiated by the substitutions
    -- generated as part of the the other constraint's solution.
    isEvaluable (Eq x y _)          = isEvaluable x && isEvaluable y
    isEvaluable (Constraint f _)    = isEvaluable f
    isEvaluable (Predicate p _)     = isEvaluable p
    isEvaluable (Not c _)           = isEvaluable c
    isEvaluable (And c d _)         = (isEvaluable c || isEvaluable d)
    isEvaluable (Or c d _)          = (isEvaluable c || isEvaluable d)
    isEvaluable (If c _ _)          = isEvaluable c
    isEvaluable (ConstraintSeq s _) = isEvaluable s

    -- evaluation of constrained elements
    eval c@(Constraint (MF id f args) err)
        | isEvaluable args = Constraint (MF id f (eval args)) err
        | otherwise        = c
    eval pred@(Predicate (MF id p args) err)
        | isEvaluable args = Predicate (MF id p (eval args)) err
        | otherwise        = pred
    eval (Eq x y err)  = Eq (eval x) (eval y) err
    eval (Not c err)   = Not (eval c) err
    eval (And c d err) = let c' = if isEvaluable c then eval c else c
                             d' = if isEvaluable d then eval d else d
                         in And c' d' err
    eval (Or c d err)  = let c' = if isEvaluable c then eval c else c
                             d' = if isEvaluable d then eval d else d
                         in Or c' d' err
    eval (If c b err)  = let c' = if isEvaluable c then eval c else c
                             b' = if isEvaluable b then eval b else b
                         in If c' b' err
    eval (ConstraintSeq s err) = ConstraintSeq (eval s) err

    -- discriminator for constraints containing meta level functions
    isMF (Eq x y _)          = isMF x || isMF y
    isMF (Constraint _ _)    = True
    isMF (Predicate _ _)     = True
    isMF (Not c _)           = isMF c
    isMF (And c d _)         = isMF c || isMF d
    isMF (Or c d _)          = isMF c || isMF d
    isMF (If c b _)          = isMF c || isMF b
    isMF (ConstraintSeq s _) = isMF s


instance (Show a, Substitutable a) => Substitutable (Constraint a) where
    apply o (Eq x y err)       = Eq (o .@. x) (o .@. y) (o .@. err)
    apply o (Constraint f err) = Constraint (o .@. f) (o .@. err)
    apply o (Predicate p err)  = Predicate (o .@. p) (o .@. err)
    apply o (Not c err)        = Not (o .@. c) (o .@. err)
    apply o (And c d err)      = And (o .@. c) (o .@. d) (o .@. err)
    apply o (Or c d err)       = Or (o .@. c) (o .@. d) (o .@. err)
    apply o (If c b err)       = If (o .@. c) (o .@. b) (o .@. err)
    apply o (ConstraintSeq s err) = ConstraintSeq (o .@. s) (o .@. err)


instance (Show a, Substitutable a,
          Instantiable a) => Instantiable (Constraint a) where
    unfold (Eq x y err)       = Eq (unfold x) (unfold y) (unfold err)
    unfold (Constraint f err) = Constraint (unfold f) (unfold err)
    unfold (Predicate p err)  = Predicate (unfold p) (unfold err)
    unfold (Not c err)        = Not (unfold c) (unfold err)
    unfold (And c d err)      = And (unfold c) (unfold d) (unfold err)
    unfold (Or c d err)       = Or (unfold c) (unfold d) (unfold err)
    unfold (If c b err)       = If (unfold c) (unfold b) (unfold err)
    unfold (ConstraintSeq s err) = ConstraintSeq (unfold s)
                                                 (unfold err)

    indexM (Eq x y err)          n = Eq (indexM x n)
                                        (indexM y n) (indexM err n)
    indexM (Constraint f err)    n = Constraint (indexM f n)
                                                (indexM err n)
    indexM (Predicate p err)     n = Predicate (indexM p n)
                                               (indexM err n)
    indexM (Not c err)           n = Not (indexM c n) (indexM err n)
    indexM (And c d err)         n = And (indexM c n)
                                         (indexM d n) (indexM err n)
    indexM (Or c d err)          n = Or (indexM c n)
                                        (indexM d n) (indexM err n)
    indexM (If c b err)          n = If (indexM c n)
                                        (indexM b n) (indexM err n)
    indexM (ConstraintSeq s err) n = ConstraintSeq (indexM s n)
                                                   (indexM err n)

    instMT (Eq x y _)          = do o <- instMT x
                                    p <- instMT (o .@. y)
                                    return (o .*. p)
    instMT (Constraint f _)    = instMT f
    instMT (Predicate p _)     = instMT p
    instMT (Not c _)           = instMT c
    instMT (And c d _)         = do o <- instMT c
                                    p <- instMT (o .@. d)
                                    return (o .*. p)
    instMT (Or c d _)          = do o <- instMT c
                                    p <- instMT (o .@. d)
                                    return (o .*. p)
    instMT (If c b _)          = do o <- instMT c
                                    p <- instMT (o .@. b)
                                    return (o .*. p)
    instMT (ConstraintSeq s _) = instMT s


instance (Eq a, Vars a) => Vars (Constraint a) where
    fv (Eq x y _)          = unions [fv x, fv y]
    fv (Constraint f _)    = fv f
    fv (Predicate p _)     = fv p
    fv (Not c _)           = fv c
    fv (And c d _)         = unions [fv c, fv d]
    fv (Or c d _)          = unions [fv c, fv d]
    fv (If c b _)          = unions [fv c, fv b]
    fv (ConstraintSeq s _) = fv s

    bv (Eq x y _)          = unions [bv x, bv y]
    bv (Constraint f _)    = bv f
    bv (Predicate p _)     = bv p
    bv (Not c _)           = bv c
    bv (And c d _)         = unions [bv c, bv d]
    bv (Or c d _)          = unions [bv c, bv d]
    bv (If c b _)          = unions [bv c, bv b]
    bv (ConstraintSeq s _) = bv s



-- | Discriminator for equality constraints.
isEq :: Eq a => Constraint a -> Bool
isEq (Eq _ _ _) = True
isEq _          = False

-- | Discriminator for predicates.
isP :: Eq a => Constraint a -> Bool
isP (Predicate _ _) = True
isP _               = False

-- | Discriminator for user-defined constraints.
isUC :: Eq a => Constraint a -> Bool
isUC (Constraint _ _) = True
isUC _                = False

-- | Getter function for the 'ErrorMsg' of a constraint.
err :: Eq a => Constraint a -> ErrorMsg
err (Eq _ _ err)          = err
err (Constraint _ err)    = err
err (Predicate _ err)     = err
err (Not _ err)           = err
err (And _ _ err)         = err
err (Or _ _ err)          = err
err (If _ _ err)          = err
err (ConstraintSeq _ err) = err

-- | Replace the error message of a constraint.
replaceErr :: Eq a => Constraint a -> ErrorMsg -> Constraint a
replaceErr (Eq c d _)          err = Eq c d err
replaceErr (Constraint f _)    err = Constraint f err
replaceErr (Predicate p _)     err = Predicate p err
replaceErr (Not c _)           err = Not c err
replaceErr (And c d _)         err = And c d err
replaceErr (Or c d _)          err = Or c d err
replaceErr (If c b _)          err = If c b err
replaceErr (ConstraintSeq s _) err = ConstraintSeq s err



-- ###################################################################
--                          Pretty Printer
-- ###################################################################

instance (Eq a, PrettyPrint a) => PrettyPrint (Constraint a) where
    pprint (Eq c d _)          = pprint c ++ " = " ++ pprint d
    pprint (Constraint f _)    = pprint f
    pprint (Predicate p _)     = pprint p
    pprint (Not c _)           = "not (" ++ pprint c ++ ")"
    pprint (And c d _)         = "(" ++ pprint c ++
                                 ") and (" ++ pprint d ++ ")"
    pprint (Or c d _)          = "(" ++ pprint c ++
                                 ") or (" ++ pprint d ++ ")"
    pprint (If c b _)          = "If " ++ pprint c ++
                                 " then " ++ pprint b
    pprint (ConstraintSeq s _) = pprint s


instance PrettyPrint Judgement where
    pprint (J ctx exp ty) = pprint ctx ++ " |- " ++
                            pprint exp ++ " : " ++ pprint ty
    pprint (C c)          = pprint c
    pprint (JSeq s)       = pprint s
    pprint (NoRule j)     = "No matching rule found for: " ++ pprint j
    pprint (Sep n)        = "---------------------------- " ++ show n


instance PrettyPrint [Judgement] where
    pprint js = intercalate "\n" (map pprint js)
