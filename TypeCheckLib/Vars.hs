{-# LANGUAGE TemplateHaskell #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Vars
-- Copyright   :  (c) 2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Type class for determining the free and bound type variable of an
-- element.
----------------------------------------------------------------------
module TypeCheckLib.Vars ( Vars (..)
                         , deriveVars
                         ) where
    
import {-# SOURCE #-} TypeCheckLib.Type
import TypeCheckLib.THUtil

import Data.Set hiding (foldr)
import Data.Sequence (Seq)
import Data.Foldable (foldr)
import Prelude hiding (foldr)
import Language.Haskell.TH


-- | Free and bound type variables.
-- Minimum complete definition: 'fv' and 'bv' or 'fv' and 'vs'
-- or 'bv' and 'vs'
class Vars a where
    -- | Free variables.
    fv :: a -> Set Ty
    fv x  = (vs x) \\ (bv x)

    -- | Bound variables.
    bv :: a -> Set Ty
    bv x = (vs x) \\ (fv x)

    -- | All variables.
    vs :: a -> Set Ty
    vs x = (fv x) `union` (bv x)


-- ###################################################################
--            `Vars' instance definitions for common types
-- ###################################################################

instance Vars () where
    fv () = empty
    bv () = empty
    vs () = empty


instance Vars Char where
    fv = const empty
    bv = const empty
    vs = const empty


instance Vars Int where
    fv = const empty
    bv = const empty
    vs = const empty


instance Vars Integer where
    fv = const empty
    bv = const empty
    vs = const empty


instance Vars Float where
    fv = const empty
    bv = const empty
    vs = const empty


instance Vars Double where
    fv = const empty
    bv = const empty
    vs = const empty


instance Vars Bool where
    fv = const empty
    bv = const empty
    vs = const empty


instance Vars Ordering where
    fv = const empty
    bv = const empty
    vs = const empty


instance Vars a => Vars [a] where
    fv = foldr (union . fv) empty
    bv = foldr (union . bv) empty
    vs = foldr (union . vs) empty


instance Vars a => Vars (Set a) where
    fv = foldr (union . fv) empty
    bv = foldr (union . bv) empty
    vs = foldr (union . vs) empty


instance Vars a => Vars (Seq a) where
    fv = foldr (union . fv) empty
    bv = foldr (union . bv) empty
    vs = foldr (union . vs) empty


instance Vars a => Vars (Maybe a) where
    fv = maybe empty fv
    bv = maybe empty bv
    vs = maybe empty vs


instance (Vars a, Vars b) => Vars (Either a b) where
    fv = either fv fv
    bv = either bv bv
    vs = either vs vs


instance (Vars a, Vars b) => Vars (a,b) where
    fv (x,y) = fv x `union` fv y
    bv (x,y) = bv x `union` bv y
    vs (x,y) = vs x `union` vs y


instance (Vars a, Vars b, Vars c) => Vars (a,b,c) where
    fv (x,y,z) = unions [fv x, fv y, fv z]
    bv (x,y,z) = unions [bv x, bv y, bv z]
    vs (x,y,z) = unions [vs x, vs y, vs z]


instance (Vars a, Vars b, Vars c, Vars d) => Vars (a,b,c,d) where
    fv (w,x,y,z) = unions [fv w, fv x, fv y, fv z]
    bv (w,x,y,z) = unions [bv w, bv x, bv y, bv z]
    vs (w,x,y,z) = unions [vs w, vs x, vs y, vs z]


instance (Vars a, Vars b, Vars c, Vars d, Vars e) =>
         Vars (a,b,c,d,e) where
    fv (v,w,x,y,z) = unions [fv v, fv w, fv x, fv y, fv z]
    bv (v,w,x,y,z) = unions [bv v, bv w, bv x, bv y, bv z]
    vs (v,w,x,y,z) = unions [vs v, vs w, vs x, vs y, vs z]


instance (Vars a, Vars b, Vars c, Vars d, Vars e, Vars f) =>
         Vars (a,b,c,d,e,f) where
    fv (u,v,w,x,y,z) = unions [fv u, fv v, fv w, fv x, fv y, fv z]
    bv (u,v,w,x,y,z) = unions [bv u, bv v, bv w, bv x, bv y, bv z]
    vs (u,v,w,x,y,z) = unions [vs u, vs v, vs w, vs x, vs y, vs z]


instance (Vars a, Vars b, Vars c, Vars d, Vars e, Vars f, Vars g) =>
         Vars (a,b,c,d,e,f,g) where
    fv (t,u,v,w,x,y,z) = unions [fv t, fv u, fv v, fv w, fv x, fv y, fv z]
    bv (t,u,v,w,x,y,z) = unions [bv t, bv u, bv v, bv w, bv x, bv y, bv z]
    vs (t,u,v,w,x,y,z) = unions [vs t, vs u, vs v, vs w, vs x, vs y, vs z]



-- ###################################################################
--    Derive instance declarations for `Vars` using Template Haskell
-- ###################################################################

-- TODO: Forall constructors

-- | Derive 'Vars' instance definitions for data type and newtype
-- declarations.
deriveVars :: Name -> Q [Dec]
deriveVars t = deriveInstDec t mkInstDec
  where
    -- make 'Vars' instance definition
    mkInstDec _ name tvs cs =
        do fvBody <- mapM mkFvCl cs
           bvBody <- mapM mkBvCl cs
           let ctx = buildCtx ''Vars tvs
               ty  = mkType (ConT name) tvs
           return [InstanceD ctx (AppT (ConT ''Vars) ty)
                                 [FunD (mkName "fv") fvBody,
                                  FunD (mkName "bv") bvBody]
                  ]

    -- TH versions of needed functions and variables
    fv = varE (mkName "fv")
    bv = varE (mkName "bv")

    -- make 'fv' clause for a constructor, i.e., apply 'fv' to all
    -- children and 'union' the resulting sets
    mkFvCl (NormalC c flds) = mkFv c (length flds)
    mkFvCl (RecC c flds)    = mkFv c (length flds)
    mkFvCl (InfixC _ c _)   = mkFv c 2

    mkFv c n = do
        (pts,vs) <- genPE n
        clause [conP c pts]
               (normalB $ appAndFold fv [| union |] [| empty |] vs) []

    -- make 'bv' clause for a constructor, i.e., apply 'bv' to all
    -- children and 'union' the resulting sets
    mkBvCl (NormalC c flds) = mkBv c (length flds)
    mkBvCl (RecC c flds)    = mkBv c (length flds)
    mkBvCl (InfixC _ c _)   = mkBv c 2

    mkBv c n = do
        (pts,vs) <- genPE n
        clause [conP c pts]
               (normalB $ appAndFold bv [| union |] [| empty |] vs) []