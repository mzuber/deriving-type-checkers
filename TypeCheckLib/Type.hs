{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Type
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module provides the library's type implementation as well as a
-- state monad carrying unused indices for fresh names.
----------------------------------------------------------------------
module TypeCheckLib.Type ( -- * Default types
                           Ty (..)
                           -- ** Auxilary functions on types
                         , (->:)
                         , (×)
                         , (**)
                         , mkT
                         , mkTV
                         , genInstOf
                         , (>=)
                           -- * Type checking monad
                         , TypeCheckM
                         , freshTV
                         , evalTypeCheckM
                         ) where

import TypeCheckLib.AbstractSyntax hiding (union)
import TypeCheckLib.Evaluable
import TypeCheckLib.Substitution
import TypeCheckLib.Unification
import TypeCheckLib.Instantiation
import TypeCheckLib.Vars

import Data.Typeable
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Data.Set (null, isSubsetOf, intersection, union)
import Data.List (intercalate)
import Data.Foldable (elem, foldrM)
import Control.Monad (liftM2)
import Control.Monad.State
import Prelude hiding ((>=), (**), elem, null)


-- ###################################################################
--                          TypeCheck Monad
-- ###################################################################

-- | During constraint generation the need for fresh type variables
-- arises. In order to be able to generate fresh names, the constraint
-- generation algorithm will run in a state monad carrying an unused
-- index.
type TypeCheckM = State Int


-- | Generate a fresh type variable.
freshTV :: TypeCheckM Ty
freshTV = do n <- get
             put (n+1)
             return $ (TV . Ide) ("$" ++ show n)


-- | Evaluate the type check monad.
evalTypeCheckM :: TypeCheckM a -> a
evalTypeCheckM m = evalState m 0



-- ###################################################################
--                      Default type implementation
-- ###################################################################

-- | Basic type implementation.
data Ty = Bottom                -- ^ Bottom type.
        | OkIn Ty               -- ^ Simple 'OkIn' type (non-indexed)
        | T Ide                 -- ^ Base type
        | TV Ide                -- ^ Type variable
        | TF Ty Ty              -- ^ Function type
        | TT [Ty]               -- ^ Tuple type
        | TC Ide [Ty]           -- ^ Type constructor
        | TS [Ty] Ty            -- ^ Type scheme
        | TyFun (MetaFun Ty)    -- ^ Function evaluating to a type
        | TySeq (Sequence Ty)   -- ^ Type sequences
        | TySet (Set Ty)        -- ^ Type sets
        | MT String             -- ^ Meta level type
          deriving (Show, Eq, Ord, Typeable)


instance AST Ty where
    index (MT id)     n = MT (id ++ show n)
    index (T id)      n = T (index id n)
    index (TV id)     n = TV (index id n)
    index (TF s t)    n = TF (index s n) (index t n)
    index (TT ts)     n = TT (indexM ts n)
    index (TC id ts)  n = TC id (indexM ts n)
    index (TS ts t)   n = TS (indexM ts n) (index t n)
    index (TyFun f)   n = TyFun (indexM f n)
    index (TySeq s)   n = TySeq (indexM s n)
    index (TySet s)   n = TySet (indexM s n)
    index t           _ = t

    (MT _) ~= (MT _) = False
    (MT _) ~= _      = True
    _      ~= _      = False

    isMeta (MT _) = True
    isMeta _      = False


instance Vars Ty where
    bv (TS tvs _) = S.fromList tvs
    bv (TyFun f)  = bv f
    bv (TySeq s)  = bv s
    bv (TySet s)  = bv s
    bv _          = S.empty

    vs tv@(TV _)  = S.singleton tv
    vs (OkIn t)   = vs t
    vs (TF s t)   = vs s `union` vs t
    vs (TT ts)    = vs ts
    vs (TC _ ts)  = vs ts
    vs (TS tvs t) = vs tvs `union` vs t
    vs (TyFun f)  = vs f
    vs (TySeq s)  = vs s
    vs (TySet s)  = vs s
    vs _          = S.empty


instance Substitutable Ty where
    apply o ok@(OkIn t)   = fromMaybe (OkIn (apply o t)) (lkup ok o)
    apply o tf@(TF s t)   = fromMaybe (TF (apply o s) (apply o t))
                                      (lkup tf o)
    apply o tt@(TT ts)    = fromMaybe (TT (apply o ts)) (lkup tt o)
    apply o tc@(TC id ts) = fromMaybe (TC id (apply o ts)) (lkup tc o)
    apply o (TyFun f)     = TyFun (apply o f)
    apply o (TySeq s)     = TySeq (apply o s)
    apply o (TySet s)     = TySet (apply o s)
    apply o ts@(TS tvs t) =
        fromMaybe (TS ((filter isTV . apply o) tvs) (apply o t))
                  (lkup ts o)
            where
              isTV (TV _) = True
              isTV _      = False
    apply o t             = app o t


instance Unifiable Ty where
    -- Unification of types
    unify t1 t2 | t1 == t2         = (True, empty)
                | t1 `occursIn` t2 = (False, empty)
                | t2 `occursIn` t1 = (False, empty)
                | otherwise        = unifyTy t1 t2

    -- Occurs check
    ty `occursIn` (OkIn t)   = ty `occursIn` t
    ty `occursIn` (TF s t)   = ty `occursIn` s || ty `occursIn` t
    ty `occursIn` (TT ts)    = foldr ((||) . (occursIn ty)) False ts
    ty `occursIn` (TC _ ts)  = foldr ((||) . (occursIn ty)) False ts
    ty `occursIn` (TS tvs t) = if ty `elem` tvs then False
                               else ty `occursIn` t
    ty `occursIn` (TySeq (ObjSeq s)) = elem ty s
    ty `occursIn` (TySet (ObjSet s)) = elem ty s
    t1 `occursIn` t2 | t1 == t2  = True
                     | otherwise = False


-- | Unification of types.
unifyTy :: Ty -> Ty -> (Bool, Substitution)
unifyTy mt@(MT _) t = (True, singleton mt t)
unifyTy t mt@(MT _) = unifyTy mt t
unifyTy tv@(TV id1) t = case t of
                          TV id2 -> if isMeta id1 || isMeta id2
                                    then unify id1 id2
                                    else (True, singleton tv t)
                          _      -> (True, singleton tv t)
unifyTy t tv@(TV _) = unifyTy tv t
unifyTy Bottom Bottom         = (True, empty)
unifyTy (OkIn t1) (OkIn t2)   = unify t1 t2
unifyTy (T id1) (T id2)       = unify id1 id2
unifyTy (TF s1 t1) (TF s2 t2) = unify [s1,t1] [s2,t2]
unifyTy (TT ts1) (TT ts2)     = unify ts1 ts2
unifyTy (TC id1 ts1) (TC id2 ts2) = unify id1 id2 `combine`
                                    unify ts1 ts2
unifyTy (TS tvs1 t1) (TS tvs2 t2) = unify t1 t2
unifyTy (TySeq s1) (TySeq s2) = unify s1 s2
unifyTy (TySet s1) (TySet s2) = unify s1 s2
unifyTy _ _ = (False, empty)


instance Instantiable Ty where
    unfold (OkIn t)   = OkIn (unfold t)
    unfold (TF s t)   = TF (unfold s) (unfold t)
    unfold (TT ts)    = TT (unfold ts)
    unfold (TC ide t) = TC ide (unfold t)
    unfold (TS tvs t) = TS (unfold tvs) (unfold t)
    unfold (TyFun f)  = TyFun (unfold f)
    unfold (TySeq s)  = TySeq (unfold s)
    unfold (TySet s)  = TySet (unfold s)
    unfold ty         = ty

    indexM = index

    instMT mt@(MT _)  = do tv <- freshTV
                           return $ singleton mt tv
    instMT (OkIn t)   = instMT t
    instMT (TF s t)   = do o <- instMT s
                           p <- instMT (o .@. t)
                           return (o .*. p)
    instMT (TT ts)    = instMT ts
    instMT (TC _ ts)  = instMT ts
    instMT (TS tvs t) = do o <- foldrM (\ t o -> do p <- instMT t
                                                    return (o .*. p)
                                       ) empty tvs
                           p <- instMT (o .@. t)
                           return (o .*. p)
    instMT (TyFun f)  = instMT f
    instMT (TySeq s)  = instMT s
    instMT (TySet s)  = instMT s
    instMT t          = return empty
    

$(deriveEvaluable ''Ty)


----------------- Auxiliary functions for default types --------------

-- | Construct function type.
(->:) :: Ty -> Ty -> Ty
t1 ->: t2 = TF t1 t2


-- | Construct binary tuple type (UTF8 version).
-- Note: this is the UTF8 symbol 'times', NOT an x.
(×) :: Ty -> Ty -> Ty
t1 × t2 = TT [t1,t2]


-- | Construct binary tuple type (ASCII version).
(**) :: Ty -> Ty -> Ty
t1 ** t2 = TT [t1,t2]


-- | Construct object level base type.
mkT :: String -> Ty
mkT = T . Ide


-- | Construct a type variable.
mkTV :: String -> Ty
mkTV = TV . Ide


-- | Check if a type is a generic instance of a given type scheme.
genInstOf :: Ty -> Ty -> Maybe (Bool, Substitution)
genInstOf = flip (>=)

-- | Check if a type is a generic instance of a given type scheme
-- (operator version).  The following identity holds: @t1 `genInstOf`
-- t2@ = @t2 >= t1@
(>=) :: Ty -> Ty -> Maybe (Bool, Substitution)
(MT _) >= _      = Nothing
_      >= (MT _) = Nothing
-- check if second type scheme is a generic instance of the first one
(TS tvs1 t1) >= (TS tvs2 t2) =
    let (b1,o) = unify t1 t2
        b2     = S.fromList (dom o) `isSubsetOf` S.fromList tvs1
        fvT1   = (fv t1) :: S.Set Ty
        bvT2   = bv t2
        b3     = null (bvT2 `intersection` fvT1)
    in Just (b1 && b2 && b3, empty)
-- or instantiate type scheme
(TS tvs t1) >= t2 =
    let f tv s = insert tv ((TV . Ide) (freshName "a")) s 
        o      = foldr f empty tvs
        t1'    = apply o t1
    in t1' >= t2
t1 >= t2@(TS _ _) = t2 >= t1
-- otherwise, unify types
t1 >= t2 = Just (unify t1 t2)


-------------------- Pretty Printer for Types ------------------------

instance PrettyPrint Ty where
    pprint Bottom     = "Bottom"
    pprint (T id)     = pprint id
    pprint (TV id)    = pprint id
    pprint (OkIn t)   = "OkIn " ++ pprint t
    pprint (TF s t)   = pprint s ++ " -> " ++ pprint t
    pprint (TT ts)    = intercalate " ** " (map pprint ts)
    pprint (TC id ts) = pprint id ++ "[" ++
                        intercalate "," (map pprint ts) ++ "]"
    pprint (TS tvs t) = "∀" ++ intercalate "," (map pprint tvs) ++
                        ". " ++ pprint t
    pprint (MT id)    = id
    pprint (TyFun f)  = pprint f
    pprint (TySeq s)  = pprint s
    pprint (TySet s)  = pprint s