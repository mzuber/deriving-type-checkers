{-# LANGUAGE TemplateHaskell #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.THUtil
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Auxiliary functions used in the the library's Template Haskell
-- functions.
----------------------------------------------------------------------
module TypeCheckLib.THUtil ( -- * Auxiliary functions
                             genPE
                           , mkConApp
                           , appAndFold
                           , appAndFold2
                           , combineExp
                           , buildCtx
                           , asTV
                           , asTVQ
                           , mkType
                           , mkTypeQ
                           , isMF
                           , conName
                           , conFlds
                           , containsSeq
                           , isSeqOver
                           , containsSet
                           , isSetOver
                           , isRec
                           , recOrSeq
                             -- * Instance declarations
                           , deriveInstDec
                           ) where


import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Data.Map as M
import Control.Monad (replicateM)


-- ###################################################################
--             Auxiliary functions for Template Haskell
-- ###################################################################

-- | Generate n fresh pattern and expression variables.
genPE :: Int -> Q ([PatQ], [ExpQ])
genPE n = do ids <- replicateM n (newName "x")
             return (map varP ids, map varE ids)


-- | Build constructor call, where `f` is apllied to all children.
mkConApp :: ExpQ -> [ExpQ] -> ExpQ -> ExpQ
mkConApp c vars f = mkCon' c (reverse vars) f
    where
      mkCon' c [] _     = c
      mkCon' c (v:vs) f = let v' = appE f v
                          in appE (mkCon' c vs f) v'


-- | Apply `f` to all expressions
--   and fold the results with `g`.
appAndFold :: Q Exp    -- ^ f
           -> Q Exp    -- ^ g
           -> Q Exp    -- ^ expression for empty variable list
           -> [Q Exp]  -- ^ variables
           -> Q Exp
appAndFold f g z []     = z
appAndFold f _ _ [v]    = appE f v
appAndFold f g z (v:vs) = [| $g $(appE f v) $(appAndFold f g z vs) |]


-- | Apply the binary function @f@ to all expressions and fold the
--   results with @g@.
appAndFold2 :: Q Exp     -- ^ f
            -> Q Exp     -- ^ g
            -> Q Exp     -- ^ expression for empty variable list
            -> [Q Exp]   -- ^ first arguments for @f@
            -> [Q Exp]   -- ^ second arguemnts for @g@
            -> Q Exp
appAndFold2 f g z []     _      = z
appAndFold2 f g z _      []     = z
appAndFold2 f _ _ [v]    [w]    = appE (appE f v) w
appAndFold2 f g z (v:vs) (w:ws) =
    [| $g $(appE (appE f v) w) $(appAndFold2 f g z vs ws) |]


-- | Combine all expressions with the given function @f@.
combineExp f z []     = z
combineExp f _ [e]    = e
combineExp f z (e:es) = appE (appE f e) (combineExp f z es)


-- | Define predicates for a given list of type variables.
buildCtx :: Name -> [TyVarBndr] -> Cxt
buildCtx nm tvs = map ((ClassP nm) . (\ v -> [asTV v])) tvs


-- | Convert bound type variables to 'normal' type variables.
asTV :: TyVarBndr -> Type
asTV (PlainTV a)    = VarT a
asTV (KindedTV a _) = VarT a


-- | Convert bound type variables to 'normal' type variables
--   (monadic version).
asTVQ :: TyVarBndr -> TypeQ
asTVQ (PlainTV a)    = varT a
asTVQ (KindedTV a _) = varT a


-- | Apply a type constructor to a given list of type variables.
mkType :: Type -> [TyVarBndr] -> Type
mkType t vars = mkType' t (reverse vars)
    where
      mkType' t [] = t
      mkType' t (v:vs) = AppT (mkType' t vs) (asTV v)


-- | Apply a type constructor to a given list of type variables 
--   (monadic version).
mkTypeQ :: TypeQ -> [TyVarBndr] -> TypeQ
mkTypeQ t vars = mkTypeQ' t (reverse vars)
    where
      mkTypeQ' t [] = t
      mkTypeQ' t (v:vs) = appT (mkTypeQ' t vs) (asTVQ v)


-- | Check if a constructor consists of one meta level function field.
isMF :: Type -> Con -> Bool
isMF ty (NormalC _ [(_, AppT (ConT s) t)]) = nameBase s == "MetaFun"
                                             && t == ty
isMF ty (RecC _ [(_,_, AppT (ConT s) t)]) = nameBase s == "MetaFun"
                                            && t == ty
isMF _ _ = False


-- | Select the name of a constructor.
conName :: Con -> Name
conName (NormalC name _)  = name
conName (RecC name _)     = name
conName (InfixC _ name _) = name
conName (ForallC _ _ con) = conName con


-- | Select the fields of a constructor.
conFlds :: Con -> [StrictType]
conFlds (NormalC _ flds)  = flds
conFlds (RecC _ flds)     = map (\ (_,s,t) -> (s,t)) flds
conFlds (InfixC f1 _ f2)  = [f1,f2]
conFlds (ForallC _ _ con) = conFlds con


-- | Check if a constructor contains a sequence over the given field.
containsSeq :: Type -> Con -> Bool
containsSeq ty (NormalC _ fs) = foldr ((||) . contains) False fs
    where
      contains (_, AppT (ConT s) t) = nameBase s == "Sequence"
                                      && t == ty
      contains _ = False
containsSeq ty (RecC _ fs)    = foldr ((||) . contains) False fs
    where
      contains (_,_, AppT (ConT s) t) = nameBase s == "Sequence"
                                        && t == ty
      contains _ = False
containsSeq _ _ = False


-- | Discriminator for sequences over a given type.
isSeqOver :: Type -> Type -> Bool
(AppT (ConT s) t) `isSeqOver` ty = nameBase s == "Sequence"
                                   && t == ty
_ `isSeqOver` _ = False


-- | Check if a constructor contains a set over the given type.
containsSet :: Type -> Con -> Bool
containsSet ty (NormalC _ fs) = foldr ((||) . contains) False fs
    where
      contains (_, AppT (ConT s) t) = nameBase s == "Set"
                                      && t == ty
      contains _ = False
containsSet ty (RecC _ fs)    = foldr ((||) . contains) False fs
    where
      contains (_,_, AppT (ConT s) t) = nameBase s == "Set"
                                        && t == ty
      contains _ = False
containsSet _ _ = False


-- | Discriminator for sequences over a given type.
isSetOver :: Type -> Type -> Bool
(AppT (ConT s) t) `isSetOver` ty = nameBase s == "Set"
                                   && t == ty
_ `isSetOver` _ = False


-- | Discriminator for recursive constructors.
-- Note: This implementation only works for monomorphic types.
isRec :: Type -> Con -> Bool
isRec ty (NormalC _ fs)   = ty `elem` (map snd fs) 
isRec ty (InfixC f1 _ f2) = ty `elem` (map snd [f1,f2])
isRec ty (RecC _ fs)      = ty `elem` (map (\ (_,_,x) -> x) fs)
isRec ty (ForallC _ _ c)  = isRec ty c


-- | Check whether a constructor contains a field of, or a set and a
-- sequence over the given type respectively.
recOrSeq :: Type -> Con -> Bool
recOrSeq ty c = isRec ty c || containsSeq ty c || containsSet ty c
      



-- ###################################################################
--           Functionality for deriving instance declarations
-- ###################################################################

-- | Generic instance declaration builder.
deriveInstDec :: Name
                 -> (Cxt -> Name -> [TyVarBndr] -> [Con] -> Q [Dec])
                 -> Q [Dec]
deriveInstDec t mkInstDec = do
  -- reify type to get all needed infos about the type and its
  -- constructors
  rt <- reify t
  
  -- build instance declaration
  case rt of
    -- for data type declarations
    TyConI (DataD cxt name tvs cs _) ->
        do instDec <- mkInstDec cxt name tvs cs
           return instDec
    -- for newtype declarations
    TyConI (NewtypeD cxt name tvs c _) ->
        do instDec <- mkInstDec cxt name tvs [c]
           return instDec
    -- error for all other declarations
    _ -> error ("Instance declarations can only be " ++
                "derived for data types and new types.")