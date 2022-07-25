{-# LANGUAGE TemplateHaskell #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Unification
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Module providing the library's unification framework, `Unifiable'
-- instance definitions for common types, as well as TH-based
-- functionality to derive `Unifiable' instance definitions for user-
-- defined data structures.
----------------------------------------------------------------------
module TypeCheckLib.Unification ( -- * Unification Framework
                                  Unifiable (..)
                                , combine
                                , (.~.)
                                , deriveUnifiable
                                ) where


import TypeCheckLib.Substitution as S
import TypeCheckLib.THUtil

import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.List (delete)
import Control.Monad (replicateM)
import Data.Foldable (toList, elem)
import Language.Haskell.TH
import Prelude hiding (elem)


-- ###################################################################
--                        Unification framework
-- ###################################################################

class Eq a => Unifiable a where
    unify :: a -> a -> (Bool, Substitution)
    unify x y = (x == y, S.empty)

    occursIn :: a -> a -> Bool
    _ `occursIn` _ = False


-- | Combining two unifiers.
combine :: (Bool, Substitution) ->
           (Bool, Substitution) -> (Bool, Substitution)
combine (b1,o) (b2,p) | b1 && b2  = (True, S.compose o p)
                      | otherwise = (False, S.empty)


-- | Checks whether two elements are unifiable.
(.~.) :: Unifiable a => a -> a -> Bool
x .~. y = fst (unify x y)



-- ###################################################################
--        `Unifiable' instance declarations for common types
-- ###################################################################

instance Unifiable ()    ; instance Unifiable Ordering
instance Unifiable Char  ; instance Unifiable Bool
instance Unifiable Int   ; instance Unifiable Integer
instance Unifiable Float ; instance Unifiable Double


instance Unifiable a => Unifiable (Maybe a) where
    unify Nothing  Nothing  = (True, S.empty)
    unify (Just x) (Just y) = unify x y
    unify _        _        = (False, S.empty)


instance (Unifiable a, Unifiable b) => Unifiable (Either a b) where
    unify (Left x)  (Left y)  = unify x y
    unify (Right x) (Right y) = unify x y
    unify _         _         = (False, S.empty)


instance (Unifiable a, Unifiable b) => Unifiable (a,b) where
    unify (x1,y1) (x2,y2) = unify x1 x2 `combine` unify y1 y2


instance (Unifiable a, Unifiable b,
          Unifiable c) => Unifiable (a,b,c) where
    unify (x1,y1,z1) (x2,y2,z2) = unify x1 x2 `combine`
                                  unify y1 y2 `combine`
                                  unify z1 z2


instance (Unifiable a, Unifiable b,
          Unifiable c, Unifiable d) => Unifiable (a,b,c,d) where
    unify (w1,x1,y1,z1) (w2,x2,y2,z2) = unify w1 w2 `combine`
                                        unify x1 x2 `combine`
                                        unify y1 y2 `combine`
                                        unify z1 z2


instance (Unifiable a, Unifiable b,
          Unifiable c, Unifiable d,
          Unifiable e) => Unifiable (a,b,c,d,e) where
    unify (v1,w1,x1,y1,z1) (v2,w2,x2,y2,z2) = unify v1 v2 `combine`
                                              unify w1 w2 `combine`
                                              unify x1 x2 `combine`
                                              unify y1 y2 `combine`
                                              unify z1 z2


instance (Unifiable a, Unifiable b,
          Unifiable c, Unifiable d,
          Unifiable e, Unifiable f) => Unifiable (a,b,c,d,e,f) where
    unify (u1,v1,w1,x1,y1,z1) (u2,v2,w2,x2,y2,z2) =
        unify u1 u2 `combine` unify v1 v2 `combine`
        unify w1 w2 `combine` unify x1 x2 `combine`
        unify y1 y2 `combine` unify z1 z2


instance (Unifiable a, Unifiable b,
          Unifiable c, Unifiable d,
          Unifiable e, Unifiable f,
          Unifiable g) => Unifiable (a,b,c,d,e,f,g) where
    unify (t1,u1,v1,w1,x1,y1,z1) (t2,u2,v2,w2,x2,y2,z2) =
        unify t1 t2 `combine` unify u1 u2 `combine`
        unify v1 v2 `combine` unify w1 w2 `combine`
        unify x1 x2 `combine` unify y1 y2 `combine` unify z1 z2



-- ###################################################################
--              Unification of lists, sets and sequences
-- ###################################################################

instance (Eq a, Substitutable a, Unifiable a) => Unifiable [a] where
    unify xs ys | length xs /= length ys = (False, S.empty)
                | otherwise = unifyLists xs ys S.empty


instance (Eq a, Substitutable a,
          Unifiable a) => Unifiable (Seq.Seq a) where
    unify s1 s2 | Seq.length s1 /= Seq.length s2 = (False, S.empty)
                | otherwise = unifyLists (toList s1) (toList s2) S.empty


instance (Eq a, Substitutable a,
          Unifiable a) => Unifiable (Set.Set a) where
    unify s1 s2 = unifySets (toList s1) (toList s2)


-- | Unification of lists.
-- Note: No check whether both lists have the same length.
unifyLists :: (Substitutable a, Unifiable a) =>
              [a] -> [a] -> Substitution -> (Bool, Substitution)
unifyLists []     []     mgu = (True, mgu)
unifyLists (x:xs) (y:ys) mgu = let (b,o) = unify x y
                               in if b then
                                      unifyLists (S.apply o xs)
                                                 (S.apply o ys)
                                                 (mgu `S.compose` o)
                                  else (False, S.empty)


-- | Unification of unordered sets (converted to lists).
unifySets :: (Substitutable a, Unifiable a) =>
             [a] -> [a] -> (Bool, Substitution)
unifySets [] [] = (True, S.empty)
unifySets s1@(x:xs) s2
    | length s1 /= length s2 = (False, S.empty)
    | otherwise = let s2'   = filter (x .~.) s2
                      y     = head s2'
                      (b,o) = unify x y
                      xs'   = S.apply o xs
                      s2''  = S.apply o (Data.List.delete y s2)
                  in if null s2' || not b
                     then (False, S.empty)
                     else (b,o) `combine` (unifySets xs' s2'')
      


-- ###################################################################
--   Derive `Unifiable` instance declarations using Template Haskell
-- ###################################################################

-- | Derive 'Unifiable' instance definitions for data type and newtype
-- declarations.
deriveUnifiable :: Name -> Q [Dec]
deriveUnifiable t = deriveInstDec t mkInstDec
    where
      -- build 'Unifiable' instance declaration
      mkInstDec cxt name tvs cs = do
        let ty        = mkType (ConT name) tvs
            unifyECls = map mkUnifyECl (filter (not . (isMF ty)) cs) ++
                        if length cs == 1 then [] else [unifyEBaseCl]
        unifyCl      <- mkUnifyCl ty unifyECls
        occursCls    <- mapM (mkOccursCl ty) (filter (recOrSeq ty) cs)
        occursBaseCl <- mkOccursBaseCl
        return [InstanceD [] (AppT (ConT ''Unifiable) ty)
                             ( (FunD (mkName "unify") [unifyCl]) :
                               if null occursCls then []
                               else [FunD (mkName "occursIn")
                                     (occursCls ++ [occursBaseCl])]
                             )
               ]

      -- TH versions of needed functions and variables
      ast       = mkName "AST"
      objSeq    = mkName "ObjSeq"
      objSet    = mkName "ObjSet"
      e1        = varE (mkName "e1")
      e2        = varE (mkName "e2")
      e1P       = varP (mkName "e1")
      e2P       = varP (mkName "e2")
      occursInE = varE (mkName "occursIn")
      empty     = varE (mkName "empty")
      singleton = varE (mkName "singleton")
      (~=)      = varE (mkName "~=")
      (=~)      = varE (mkName "=~")
      isMeta    = varE (mkName "isMeta")
      unifyE    = varE (mkName "unifyE")

      
      -- Build 'unify' function clause using the following pattern:
      -- unify e1 e2 | e1 == e2         = (True, empty)
      --             | e1 `occursIn` e2 = (False, empty)
      --             | e2 `occursIn` e1 = (False, empty)
      --             | e1 ~= e2         = (True, singleton e1 e2)
      --             | e1 =~ e2         = (True, singleton e2 e1)
      --             | otherwise        = unifyE e1 e2
      --     where
      --         unifyE = ...
      mkUnifyCl ty unifyECls = do
          isAst <- isInstance ast [ty]
          clause [ e1P, e2P ]
                 ( guardedB (
                   [ normalGE [| $e1 == $e2 |]
                              [| (True, $empty ) |] ,
                     normalGE [| $e1 `occursIn` $e2 |]
                              [| (False, $empty ) |] ,
                     normalGE [| $e2 `occursIn` $e1 |]
                              [| (False, $empty ) |]
                   ]
                   ++
                   ( if isAst then
                   [ normalGE [| $((~=)) $e1 $e2 |]
                              [| (True, $singleton $e1 $e2 ) |] ,
                     normalGE [| $((=~)) $e1 $e2 |]
                              [| (True, $singleton $e2 $e1 ) |]
                   ]
                   else [] )
                   ++
                   [ normalGE [| otherwise |]
                              [| $unifyE $e1 $e2 |]
                   ] )
                 ) [ funD (mkName "unifyE") unifyECls ]

      -- build 'unifyE' function clause for a constructor
      mkUnifyECl (NormalC c fs)  = mkUnifyE c (length fs)
      mkUnifyECl (RecC c fs)     = mkUnifyE c (length fs)
      mkUnifyECl (InfixC _ c _)  = mkUnifyE c 2
      mkUnifyECl (ForallC _ _ _) = error "Not supported yet."

      -- using the following pattern:
      -- unifyE e1@(A x1) e2@(A x2)
      --     | isMeta e1 = (True, singleton e1 e2)
      --     | otherwise = unify x1 x2
      -- unifyE e1@(B x1 y1) e2@(B x2 y2)
      --     | isMeta e1 = (True, singleton e1 e2)
      --     | otherwise = unify x1 x2 `combine` unify y1 y2
      mkUnifyE c n = do
          (pts1,vs1) <- genPE n
          (pts2,vs2) <- genPE n
          clause [asP (mkName "e1") (conP c pts1),
                  asP (mkName "e2") (conP c pts2)]
                 (guardedB
                  [ normalGE (appE isMeta e1)
                             [| (True, $singleton $e1 $e2) |],
                    normalGE [| otherwise |]
                             (appAndFold2 [| unify |] [| combine |]
                                          [| (True, $empty ) |]
                                          vs1 vs2)
                  ]
                 ) []

      -- and the following base clause:
      -- unifyE _ _ = False
      unifyEBaseCl =
          clause [wildP, wildP] (normalB [| (False, $empty ) |]) []


      -- build 'occursIn' function clause for a constructor
      mkOccursCl ty (NormalC c fs)   = mkOccurs c (map snd fs) ty
      mkOccursCl ty (InfixC f1 c f2) = mkOccurs c (map snd [f1,f2]) ty
      mkOccursCl ty (RecC c fs)      =
          mkOccurs c (map (\ (_,_,x) -> x) fs) ty
      mkOccursCl ty (ForallC _ _ _)  = error "Not supported yet."

      -- using this pattern for recursive types:
      -- e `occursIn` (A e1 e2) = e `occursIn` e1 || e `occursIn` e2
      -- e `occursIn` (B e1)    = e `occursIn` e1
      --
      -- and this one for sets and sequences:
      -- e `occursIn` (ESeq (ObjSeq s)) = elem e s
      -- e `occursIn` (ESet (ObjSet s)) = elem e s
      mkOccurs c ts ty = do
          let e = mkName "e"
          (pts,vs) <- genPatExpOccursIn ts ty (varE e)
          clause [varP e, conP c pts]
                 (normalB (combineExp [| (||) |] [| True |] vs)
                 ) []

      genPatExpOccursIn []     _  _ = return ([], [])
      genPatExpOccursIn (t:ts) ty e = do
          ide        <- newName "x"
          (pts,exps) <- genPatExpOccursIn ts ty e
          let (pt,exp) = mkPE e ty t ide
          return (pt:pts, exp:exps)

      mkPE e ty t ide
          | t == ty          = ( varP ide ,
                                 [| $e `occursIn` $(varE ide) |] )
          | t `isSeqOver` ty = ( conP objSeq [varP ide] ,
                                 [| elem $e $(varE ide) |] )
          | t `isSetOver` ty = ( conP objSet [varP ide] ,
                                 [| elem $e $(varE ide) |] )
          | otherwise        = ( wildP , [| False |] )
          

      -- and the following base clause:
      -- e1 `occursIn` e2 | e1 == e2  = True
      --                  | otherwise = False
      mkOccursBaseCl =
          clause [e1P, e2P]
                 (guardedB [ normalGE [| $e1 == $e2 |]
                                      [| True |],
                             normalGE [| otherwise |]
                                      [| False |]
                           ]
                 ) []