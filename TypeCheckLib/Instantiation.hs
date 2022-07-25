{-# LANGUAGE TemplateHaskell, DoAndIfThenElse #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Instantiation
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Module providing the library's instantiation framework,
-- `Instantiable' instance definitions for common types, as well as
-- TH-based functionality to derive `Instantiable' instance
-- definitions for user-defined data structures.
----------------------------------------------------------------------
module TypeCheckLib.Instantiation where

import TypeCheckLib.Substitution
import {-# SOURCE #-} TypeCheckLib.Type (TypeCheckM)
import TypeCheckLib.THUtil

import Language.Haskell.TH
import qualified Data.Sequence
import qualified Data.Set
import Data.List (nub)
import Data.Typeable
import Data.Foldable (foldrM)
import Control.Monad (liftM2)

-- ###################################################################
--                      Instantiation framework
-- ###################################################################

class (Eq a, Typeable a) => Instantiable a where
    -- | Unfolding of meta level sets and sequences.
    unfold :: a -> a
    unfold = id
    -- | Indexing of meta level elements.
    indexM :: a -> Int -> a
    indexM x _ = x
    -- | Instantiation of meta level types.
    instMT :: a -> TypeCheckM Substitution
    instMT = const (return empty)



-- ###################################################################
--        `Instantiable' instance declarations for common types
-- ###################################################################

instance Instantiable ()    ; instance Instantiable Ordering
instance Instantiable Char  ; instance Instantiable Bool
instance Instantiable Int   ; instance Instantiable Integer
instance Instantiable Float ; instance Instantiable Double


instance (Substitutable a, Instantiable a) => Instantiable [a] where
    unfold      = map unfold
    indexM xs n = map ((flip indexM) n) xs
    instMT      = foldrM ( \ x o -> do p <- instMT (o .@. x)
                                       return (o .*. p)
                         ) empty


instance Instantiable a => Instantiable (Maybe a) where
    unfold     = maybe Nothing (Just . unfold)
    indexM x n = maybe Nothing (Just . ((flip indexM) n)) x
    instMT     = maybe (return empty) instMT


instance (Instantiable a,
          Instantiable b) => Instantiable (Either a b) where
    unfold     = either (Left . unfold) (Right . unfold)
    indexM x n = either (Left . ((flip indexM) n))
                        (Right . ((flip indexM) n)) x
    instMT     = either instMT instMT


instance (Substitutable a,
          Instantiable a) => Instantiable (Data.Sequence.Seq a) where
    unfold     = fmap unfold
    indexM s n = fmap ((flip indexM) n) s
    instMT     = foldrM ( \ x o -> do p <- instMT (o .@. x)
                                      return (o .*. p)
                        ) empty


instance (Ord a, Substitutable a,
          Instantiable a) => Instantiable (Data.Set.Set a) where
    unfold     = Data.Set.map unfold
    indexM s n = Data.Set.map ((flip indexM) n) s
    instMT     = foldrM ( \ x o -> do p <- instMT (o .@. x)
                                      return (o .*. p)
                        ) empty


instance (Instantiable a,
          Instantiable b) => Instantiable (a,b) where
    unfold (x,y)   = (unfold x, unfold y)
    indexM (x,y) n = (indexM x n, indexM y n)
    instMT (x,y)   = liftM2 (.*.) (instMT x) (instMT y)


instance (Instantiable a, Instantiable b,
          Instantiable c) => Instantiable (a,b,c) where
    unfold (x,y,z)   = (unfold x, unfold y, unfold z)
    indexM (x,y,z) n = (indexM x n, indexM y n, indexM z n)
    instMT (x,y,z)   = liftM2 (.*.) (instMT x) $
                       liftM2 (.*.) (instMT y) (instMT z)


instance (Instantiable a, Instantiable b,
          Instantiable c, Instantiable d) =>
         Instantiable (a,b,c,d) where
    unfold (w,x,y,z)   = (unfold w, unfold x,
                          unfold y, unfold z)
    indexM (w,x,y,z) n = (indexM w n, indexM x n,
                          indexM y n, indexM z n)
    instMT (w,x,y,z)   = liftM2 (.*.) (instMT w) $
                         liftM2 (.*.) (instMT x) $
                         liftM2 (.*.) (instMT y) (instMT z)


instance (Instantiable a, Instantiable b,
          Instantiable c, Instantiable d,
          Instantiable e) => Instantiable (a,b,c,d,e) where
    unfold (v,w,x,y,z)   = (unfold v, unfold w,
                            unfold x, unfold y, unfold z)
    indexM (v,w,x,y,z) n = (indexM v n, indexM w n,
                            indexM x n, indexM y n, indexM z n)
    instMT (v,w,x,y,z)   = liftM2 (.*.) (instMT v) $
                           liftM2 (.*.) (instMT w) $
                           liftM2 (.*.) (instMT x) $
                           liftM2 (.*.) (instMT y) (instMT z)


instance (Instantiable a, Instantiable b,
          Instantiable c, Instantiable d,
          Instantiable e, Instantiable f) =>
         Instantiable (a,b,c,d,e,f) where
    unfold (u,v,w,x,y,z)   = (unfold u, unfold v, unfold w,
                              unfold x, unfold y, unfold z)
    indexM (u,v,w,x,y,z) n = (indexM u n, indexM v n, indexM w n,
                              indexM x n, indexM y n, indexM z n)
    instMT (u,v,w,x,y,z)   = liftM2 (.*.) (instMT u) $
                             liftM2 (.*.) (instMT v) $
                             liftM2 (.*.) (instMT w) $
                             liftM2 (.*.) (instMT x) $
                             liftM2 (.*.) (instMT y) (instMT z)


instance (Instantiable a, Instantiable b,
          Instantiable c, Instantiable d,
          Instantiable e, Instantiable f,
          Instantiable g) => Instantiable (a,b,c,d,e,f,g) where
    unfold (t,u,v,w,x,y,z)   = (unfold t, unfold u, unfold v,
                                unfold w, unfold x, unfold y,
                                unfold z)
    indexM (t,u,v,w,x,y,z) n = (indexM t n, indexM u n, indexM v n,
                                indexM w n, indexM x n, indexM y n,
                                indexM z n)
    instMT (t,u,v,w,x,y,z)   = liftM2 (.*.) (instMT t) $
                               liftM2 (.*.) (instMT u) $
                               liftM2 (.*.) (instMT v) $
                               liftM2 (.*.) (instMT w) $
                               liftM2 (.*.) (instMT x) $
                               liftM2 (.*.) (instMT y) (instMT z)



-- ###################################################################
--  Derive `Instantiable` instance declarations using Template Haskell
-- ###################################################################

-- TODO: Forall constructors

-- | Derive 'Instantiable' instance definitions for data type and
-- newtype declarations.
deriveInstantiable :: Name -> Q [Dec]
deriveInstantiable t = deriveInstDec t mkInstDec
    where
      -- build 'Instantiable' instance declaration
      mkInstDec _ name tvs cs = do
          let ty  = mkType (ConT name) tvs
              ctx = buildCtx ''Instantiable tvs
        
          unfoldBody <- mapM mkUnfoldCl cs
          indexMBody <- mapM (\ c -> mkIndexMCl c ty) cs
          instMTBody <- mapM (\ c -> mkInstMTCl c) cs
          
          return [InstanceD ctx (AppT (ConT ''Instantiable) ty)
                                [FunD (mkName "unfold") unfoldBody,
                                 FunD (mkName "indexM") (nub indexMBody),
                                 FunD (mkName "instMT") (nub instMTBody)]]


      -- TH versions of needed functions and names
      unfold = varE (mkName "unfold")
      indexM = varE (mkName "indexM")
      index  = varE (mkName "index")
      instMT = varE (mkName "instMT")
      empty  = varE (mkName "empty")
      comp   = varE (mkName "compose")
      ast    = mkName "AST"


      -- build unfold clause for a constructor
      mkUnfoldCl (NormalC c fs) = mkUnfold c (length fs)
      mkUnfoldCl (RecC c fs)    = mkUnfold c (length fs)
      mkUnfoldCl (InfixC _ c _) = mkUnfold c 2

      -- by applying unfold to all children, i.e.,
      -- unfold (C a b) = C (unfold a) (unfold b)
      mkUnfold c n = do
          (pts,vs) <- genPE n
          clause [conP c pts] (normalB (mkConApp (conE c) vs unfold)) []


      -- build indexM clause for a constructor
      mkIndexMCl (NormalC c fs) ty = mkIndexM c (length fs) ty
      mkIndexMCl (RecC c fs)    ty = mkIndexM c (length fs) ty
      mkIndexMCl (InfixC _ c _) ty = mkIndexM c 2 ty

      -- if an AST instance for T is given, use the AST `index'
      -- function, otherwise apply indexM to all children
      mkIndexM c nFs ty = do
          isAST    <- isInstance ast [ty]
          (pts,vs) <- genPE nFs
          let n = mkName "n"
          if isAST then
              clause [] (normalB index) []
          else
              clause [conP c pts, varP n]
                     (normalB (mkConApp (conE c) vs
                              (appE indexM (varE n)))
                     ) []


      -- build instMT clause for a constructor
      mkInstMTCl (NormalC c fs) = mkInstMT c (length fs)
      mkInstMTCl (RecC c fs)    = mkInstMT c (length fs)
      mkInstMTCl (InfixC _ c _) = mkInstMT c 2

      -- if a Type instance for T is given, use the Type `inst'
      -- function, otherwise apply instMT to all children and
      -- compose the resulting substitutions
      mkInstMT c n = do
          (pts,vs) <- genPE n
          clause [conP c pts] (normalB
                               (appAndFold instMT [| liftM2 $comp |]
                                           [| return $empty |] vs)
                              ) []