{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables,
             DeriveDataTypeable #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Context
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Heterogenous contexts.
----------------------------------------------------------------------
module TypeCheckLib.Context ( Context (..)
                            , empty
                            , insert
                            , singleton
                            , fromList
                            , fromSeq
                            , delete
                            , lkup
                            , union
                            ) where

import TypeCheckLib.AbstractSyntax hiding (union)
import TypeCheckLib.Type
import TypeCheckLib.Evaluable
import TypeCheckLib.Substitution (Substitutable)
import qualified TypeCheckLib.Substitution as S
import TypeCheckLib.Unification
import TypeCheckLib.Instantiation
import TypeCheckLib.Vars

import qualified Data.Set as Set
import Data.List (intercalate)
import Data.Maybe (fromJust, fromMaybe)
import Data.Foldable (toList)
import Data.Typeable


-- ###################################################################
--           Wrapper for expressions and types in contexts
-- ###################################################################

-- | Wrapper for expressions contained in a context.
data E = forall a . (Show a, Eq a, Ord a, Typeable a,
                     AST a, PrettyPrint a) => E a
         deriving Typeable

instance Show E where
    show (E e) = show e

instance Eq E where
    (E x) == (E (y :: a)) = case (cast x) :: Maybe a of
                              Nothing -> False
                              Just x' -> x' == y

instance Ord E where
    (E x) < (E (y :: a)) = case (cast x) :: Maybe a of
                             Nothing -> False
                             Just x' -> x' < y

instance PrettyPrint E where
    pprint (E e) = pprint e



-- ###################################################################
--                 Contexts based on association list
-- ###################################################################

-- | A 'Context' is a association list of mappings
-- from expressions to types.
data Context = Ctx [(E,Ty)]                -- ^ Context
             | MCtx String                 -- ^ Meta level context
             | CtxFun (MetaFun Context)    -- ^ Meta level function
                                           -- evaluating to a context
               deriving (Show, Eq, Ord, Typeable)


instance AST Context where
    index (MCtx id) n = MCtx (id ++ show n)
    index ctx       _ = ctx

    (MCtx _) ~= ctx | isMeta ctx = False
                    | otherwise  = True
    _ ~= _ = False

    isMeta (MCtx _) = True
    isMeta _        = False


instance Vars Context where
    vs (Ctx ctx)  = foldr (Set.union . vs . snd) Set.empty ctx
    vs (CtxFun f) = vs f
    vs _          = Set.empty

    fv (Ctx ctx)  = foldr (Set.union . fv . snd) Set.empty ctx
    fv (CtxFun f) = fv f
    fv _          = Set.empty


instance Evaluable Context where
    isEvaluable (Ctx _)    = True
    isEvaluable (MCtx _)   = False
    isEvaluable (CtxFun f) = isEvaluable f

    eval c@(CtxFun (MF id f args))
        | isEvaluable args = fromMaybe c (f (eval args))
        | otherwise        = c
    eval ctx = ctx

    isMF (CtxFun f) = True
    isMF _          = False


instance Substitutable Context where
    apply o (CtxFun f) = CtxFun (S.apply o f)
    apply o ctx = S.app o ctx


instance Unifiable Context where
    unify m@(MCtx _) ctx    = (True, S.singleton m ctx)
    unify ctx m@(MCtx _)    = unify m ctx
    unify (Ctx c1) (Ctx c2) = (c1 == c2, S.empty)
    unify (CtxFun _) (CtxFun _) = error "Can't unify meta functions."


instance Instantiable Context where
    unfold (CtxFun f) = CtxFun (unfold f)
    unfold ctx        = ctx

    instMT (CtxFun f) = instMT f
    instMT _          = return S.empty


instance PrettyPrint Context where
    pprint (Ctx [])   = "{}"
    pprint (Ctx ctx)  = "{" ++ intercalate ", " (map pprint ctx) ++ "}"
    pprint (MCtx ide) = ide
    pprint (CtxFun f) = pprint f


-- | Empty context.
empty :: Context
empty = Ctx []


-- | Add a typing for an expression to a given context.
insert :: (Show a, Ord a, Typeable a, AST a, PrettyPrint a) =>
          a -> Ty -> Context -> Maybe Context
insert _ _ (MCtx _)   = Nothing
insert _ _ (CtxFun _) = Nothing
insert e t ctx = let (Ctx ctx') = fromJust (delete e ctx)
                 in Just $ Ctx (ctx' ++ [(E e, t)])


-- | Context containing a single typing for an expression.
singleton :: (Show a, Ord a, Typeable a, AST a, PrettyPrint a) =>
             a -> Ty -> Context
singleton e t = fromJust (insert e t empty)


-- | Build a context from a given list of typings.
fromList :: (Show a, Ord a, Typeable a, AST a, PrettyPrint a) =>
            [(a, Ty)] -> Context
fromList ts = Ctx (map (\ (e,t) -> (E e, t)) ts)


-- | Build a context from a given sequence of typings.
fromSeq :: (Show a, Ord a, Typeable a, AST a, PrettyPrint a) =>
           Sequence (a, Ty) -> Maybe Context
fromSeq (MetaSeq _ _) = Nothing
fromSeq (ObjSeq s)    = Just (fromList (toList s))


-- | Delete the mapping containing the given expression from a context.
delete :: (Show a, Ord a, Typeable a, AST a, PrettyPrint a) =>
          a -> Context -> Maybe Context
delete _ (MCtx _)   = Nothing
delete _ (CtxFun _) = Nothing
delete e (Ctx ctx)  = Just $ Ctx (deleteE (E e) ctx)

deleteE e ctx = filter (\ (e',_) -> e /= e') ctx


-- | Lookup the type of an expression in a given context.
lkup :: (Show a, Ord a, Typeable a, AST a, PrettyPrint a) =>
        a -> Context -> Maybe Ty
lkup _ (MCtx _) = Nothing
lkup _ (CtxFun _) = Nothing
lkup e (Ctx ctx) = lkup' e ctx
    where
      lkup' _ [] = Nothing
      lkup' e ((e',ty):ctx) | (E e) == e' = Just ty
                            | otherwise   = lkup' e ctx


-- | Right-biased union of two contexts.
union :: Context -> Context -> Maybe Context
union (Ctx c1) (Ctx c2) =
    Just $ Ctx ((c1 `without` (map fst c2)) ++ c2)
        where
          c1 `without` c2 = foldl (flip deleteE) c1 c2
union _ _ = Nothing