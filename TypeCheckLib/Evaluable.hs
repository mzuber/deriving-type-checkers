{-# LANGUAGE TemplateHaskell, DoAndIfThenElse #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Evaluable
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Module providing the library's evaluation framework, `Evaluable'
-- instance definitions for common types, as well as TH-based
-- functionality to derive `Evaluable' instance definitions for user-
-- defined data structures.
----------------------------------------------------------------------
module TypeCheckLib.Evaluable ( -- * Evaluation Framework
                                Evaluable (..)
                              , deriveEvaluable
                              ) where

import TypeCheckLib.THUtil hiding (isMF)
import qualified TypeCheckLib.THUtil as THUtil (isMF)

import Language.Haskell.TH
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as S (map)
import Data.Sequence (Seq)
import Data.Foldable (foldr)
import Data.Functor (fmap)
import Prelude hiding (foldr)


-- | The type class 'Evaluable' is used to determine whether the
-- wrapped up arguments of meta level function calls and constraints
-- are evaluable (at object level) or still contain meta level
-- elements.
class Evaluable a where
    -- | Discriminator for object level elements.
    isEvaluable :: a -> Bool
    isEvaluable = const True

    -- | 'eval' evaluates wrapped up meta level function
    -- calls if all arguments are at object level.
    eval :: a -> a
    eval = id

    -- | Discriminator for elements containing meta level functions.
    isMF :: a -> Bool
    isMF = const False



-- ###################################################################
--         `Evaluable' instance definitions for common types
-- ###################################################################

instance Evaluable ()    ; instance Evaluable Ordering
instance Evaluable Char  ; instance Evaluable Bool
instance Evaluable Int   ; instance Evaluable Integer
instance Evaluable Float ; instance Evaluable Double


instance Evaluable a => Evaluable [a] where
    isEvaluable = foldr ((&&) . isEvaluable) True
    eval = map eval
    isMF = foldr ((||) . isMF) False


instance (Ord a, Evaluable a) => Evaluable (Set a) where
    isEvaluable = foldr ((&&) . isEvaluable) True
    eval = S.map eval
    isMF = foldr ((||) . isMF) False


instance Evaluable a => Evaluable (Seq a) where
    isEvaluable = foldr ((&&) . isEvaluable) True
    eval = fmap eval
    isMF = foldr ((||) . isMF) False


instance Evaluable a => Evaluable (Maybe a) where
    isEvaluable = maybe True isEvaluable
    eval = maybe Nothing (Just . eval)
    isMF = maybe False isMF


instance (Evaluable a, Evaluable b) => Evaluable (Either a b) where
    isEvaluable = either isEvaluable isEvaluable
    eval = either (Left . eval) (Right . eval)
    isMF = either isMF isMF


instance (Evaluable a, Evaluable b) => Evaluable (a,b) where
    isEvaluable (x,y) = isEvaluable x && isEvaluable y
    eval (x,y)        = (eval x, eval y)
    isMF (x,y)        = isMF x || isMF y


instance (Evaluable a, Evaluable b,
          Evaluable c) => Evaluable (a,b,c) where
    isEvaluable (x,y,z) = isEvaluable x &&
                          isEvaluable y && isEvaluable z
    eval (x,y,z)        = (eval x, eval y, eval z)
    isMF (x,y,z)        = isMF x || isMF y || isMF z


instance (Evaluable a, Evaluable b,
          Evaluable c, Evaluable d) => Evaluable (a,b,c,d) where
    isEvaluable (w,x,y,z) = isEvaluable w && isEvaluable x &&
                            isEvaluable y && isEvaluable z
    eval (w,x,y,z)        = (eval w, eval x, eval y, eval z)
    isMF (w,x,y,z)        = isMF w || isMF x || isMF y || isMF z


instance (Evaluable a, Evaluable b, Evaluable c,
          Evaluable d, Evaluable e) => Evaluable (a,b,c,d,e) where
    isEvaluable (v,w,x,y,z) = isEvaluable v && isEvaluable w &&
                              isEvaluable x && isEvaluable y &&
                              isEvaluable z
    eval (v,w,x,y,z)        = (eval v, eval w,
                               eval x, eval y, eval z)
    isMF (v,w,x,y,z)        = isMF v || isMF w || isMF x ||
                              isMF y || isMF z


instance (Evaluable a, Evaluable b,
          Evaluable c, Evaluable d,
          Evaluable e, Evaluable f) => Evaluable (a,b,c,d,e,f) where
    isEvaluable (u,v,w,x,y,z) = isEvaluable u && isEvaluable v &&
                                isEvaluable w && isEvaluable x &&
                                isEvaluable y && isEvaluable z
    eval (u,v,w,x,y,z)        = (eval u, eval v, eval w,
                                 eval x, eval y, eval z)
    isMF (u,v,w,x,y,z)        = isMF u || isMF v || isMF w ||
                                isMF x || isMF y || isMF z


instance (Evaluable a, Evaluable b,
          Evaluable c, Evaluable d,
          Evaluable e, Evaluable f,
          Evaluable g) => Evaluable (a,b,c,d,e,f,g) where
    isEvaluable (t,u,v,w,x,y,z) = isEvaluable t && isEvaluable u &&
                                  isEvaluable v && isEvaluable w &&
                                  isEvaluable x && isEvaluable y &&
                                  isEvaluable z
    eval (t,u,v,w,x,y,z)        = (eval t, eval u, eval v,
                                   eval w, eval x, eval y, eval z)
    isMF (t,u,v,w,x,y,z)        = isMF t || isMF u || isMF v || isMF w
                                  || isMF x || isMF y || isMF z



-- ###################################################################
-- Derive instance declarations for `Evaluable` using Template Haskell
-- ###################################################################

-- TODO: Forall constructors

-- | Derive 'Evaluable' instance definitions for data type and newtype
-- declarations.
deriveEvaluable :: Name -> Q [Dec]
deriveEvaluable t = deriveInstDec t mkInstDec
  where
    -- make Evaluable instance definition
    mkInstDec _ name tvs cs =
        do evalBody <- mapM (\ c -> mkEval c name tvs) cs
           isEvaluableBody <- mapM (\ c -> mkIsEvaluable c name tvs) cs
           isMFBody <- mapM (\ c -> mkIsMF c name tvs) cs
           let ctx = buildCtx ''Evaluable tvs
               ty  = mkType (ConT name) tvs
           return [InstanceD ctx (AppT (ConT ''Evaluable) ty)
                                 [FunD (mkName "eval") evalBody
                                 ,FunD (mkName "isEvaluable") isEvaluableBody
                                 ,FunD (mkName "isMF") isMFBody
                                 ]
                  ]


    -- names for the MetaFun type, the Evaluable type class and some
    -- variables
    metafun = mkName "MetaFun"
    mf      = mkName "MF"
    ast     = mkName "AST"
    f       = mkName "f"
    args    = mkName "args"
    c       = mkName "c"

    isEvaluable = varE (mkName "isEvaluable")
    eval        = varE (mkName "eval")
    isMF        = varE (mkName "isMF")
    isMeta      = varE (mkName "isMeta")


    -- make `eval` clause for a constructor
    mkEval c t tvs | THUtil.isMF (mkType (ConT t) tvs) c =
                       mfClause (conName c)
                   | otherwise = cClause (conName c) (conFlds c)

    -- build `eval` clause for constructors containing a meta level
    -- function, e.g.,
    -- eval c@(C (MF _ f args))
    --     | isEvaluable args = fromMaybe c (f (eval args))
    --     | otherwise        = c
    mfClause cName =
        clause [asP c (conP cName [conP mf [wildP,
                                            varP f,
                                            varP args]])]
               (guardedB
                [ normalGE (appE isEvaluable (varE args))
                           [| fromMaybe $(varE c)
                              ( $(varE f) ($eval $(varE args)) ) |],
                  normalGE [| otherwise |] (varE c) ]
               ) []

    -- build `eval` clause for every other constructor,
    -- i.e., apply `eval` to all children
    cClause c fs = do
        -- get variables for left and right side of funciton definition
        (pats,vars) <- genPE (length fs)
        -- generate function clause for constructor
        clause [conP c pats] (normalB (mkConApp (conE c) vars eval)) []


    -- build `isEvaluable` clause for a constructor, e.g.,
    -- isEvaluable c@(C a b) | isMeta c  = False
    --                       | otherwise = isEvaluable a && isEvaluable b
    mkIsEvaluable c t tvs  = let n = length (conFlds c)
                             in mkIsEvaluable' (conName c) n t tvs

    mkIsEvaluable' cName n t tvs = do
        isAST <- isInstance ast [ConT t]
        (pts,vs) <- genPE n
        if isAST then
            clause [asP c (conP cName pts)]
                   (guardedB [ normalGE (appE isMeta (varE c)) [| False |],
                               normalGE [| otherwise |] (mkIsEvaluableApp vs) ]
                   ) []
        else clause [conP cName pts] (normalB (mkIsEvaluableApp vs)) []

    -- apply `eval` to all children
    mkIsEvaluableApp = appAndFold isEvaluable [| (&&) |] [| True |]


    -- make `isMF` clause for a constructor, i.e.,
    --    isMF (C (MF _ _ _)) = True
    --    isMF (C x y)        = isMF x || isMF y
    mkIsMF c t tvs | THUtil.isMF (mkType (ConT t) tvs) c =
                       clause [conP (conName c) [wildP]]
                              (normalB [| True |]) []
                   | otherwise =
                       do (pts,vs) <- genPE $ length (conFlds c)
                          clause [conP (conName c) pts]
                                 (normalB (appAndFold isMF [| (||) |]
                                                      [| False |] vs)
                                 ) []