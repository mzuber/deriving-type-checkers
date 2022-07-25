{-# LANGUAGE TemplateHaskell, ExistentialQuantification,
             ScopedTypeVariables, DeriveDataTypeable #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Substitution
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- As part of this library, the main purpose of substitutions is the
-- mapping from meta level elements to their respective object level
-- pendants. This module provides the library's framework for the
-- application and composition of substitutions as well as
-- functionality to generate fresh names for variables and types.
----------------------------------------------------------------------
module TypeCheckLib.Substitution ( -- * Substitutions
                                   Substitution
                                 , S(..)
                                 , empty
                                 , (|->)
                                 , singleton
                                 , insert
                                 , fromList
                                 , fromMap
                                 , delete
                                 , lkup
                                 , dom
                                 , ran
                                 , app
                                 , compose
                                   -- * Substitution framework
                                 , Substitutable (apply)
                                 , (.@.)
                                 , (.*.)
                                 , deriveSubstitutable
                                   -- * Fresh name supply
                                 , freshName
                                 ) where

-- import qualified TypeCheckLib.AssocList as AL
import TypeCheckLib.THUtil

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Set
import qualified Data.Sequence
import Language.Haskell.TH
import Data.Foldable
import Data.Typeable
import Control.Concurrent.MVar
import System.IO.Unsafe


-- ###################################################################
--                       Substitution Framework
-- ###################################################################

-- | Substitution framwwork.
class (Ord a, Typeable a) => Substitutable a where
    -- | Apply a substitution to a given element.
    apply :: Substitution -> a -> a
    apply o x = app o x


-- | Operator version of 'apply'.
(.@.) :: Substitutable a => Substitution -> a -> a
o .@. x = apply o x


-- | Composition of two 'Substitution's.
(.*.) :: Substitution -> Substitution -> Substitution
(.*.) = compose



-- ###################################################################
--                     Heterogenous Substitutions
-- ###################################################################

-- | Existential quantified wrapper for map-based, homogenous
-- substitutions.
data S = forall a . (Typeable a, Show a, Ord a, Substitutable a) =>
         S (Map a a)
         deriving Typeable

instance Eq S where
    (S m1) == (S (m2 :: Map a a)) =
        case (cast m1) :: Maybe (Map a a) of
          Nothing -> False
          Just m1' -> m1' == m2

instance Show S where
    show (S m) = "{" ++ L.intercalate "," s ++ "}"
        where
          s = L.map (\ (k,v) -> show k ++ " ~> " ++ show v)
                    (M.toList m)


-- | A 'Substitution' encapsulates multiple homogenous substitutions.
type Substitution = Map TypeRep S


-- | Empty substitution.
empty :: Substitution
empty = M.empty


-- | Construct a substitution containing the given mapping.
(|->) :: (Typeable a, Show a, Eq a, Ord a, Substitutable a) =>
         a -> a -> Substitution
(|->) = singleton


-- | See '|->'.
singleton :: (Typeable a, Show a, Eq a, Ord a, Substitutable a) =>
             a -> a -> Substitution
singleton k v = insert k v empty


-- | Add a key and the corresponding value to a 'Substitution'. If a
-- substitution ranging over the type of key and value already exists,
-- key and value are inserted to this substitution
-- accordingly. Otherwise, a new entry is added to the underlying list
-- consisting of key and value's type and a new substituion.
insert :: (Typeable a, Show a, Eq a, Ord a, Substitutable a) =>
          a -> a -> Substitution -> Substitution
insert k v s = M.insertWith addKV (typeOf k) (S (M.singleton k v)) s
    where
      addKV _ (S m) = case (cast m) :: Typeable a => Maybe (Map a a) of
                        Just m' -> S (M.insert k v m')
                        _       -> error "Corrupt substitution"


-- | Construct a 'Substitution' from a given list of mappings.
fromList :: (Typeable a, Show a, Eq a, Ord a, Substitutable a) =>
            [(a,a)] -> Substitution
fromList = L.foldr (uncurry insert) empty


-- | Construct a 'Substitution' from given mappings.
fromMap :: (Typeable a, Show a, Eq a, Ord a, Substitutable a) =>
           Map a a -> Substitution
fromMap = fromList . M.toList


-- | Delete all mappings containing the given key from a substitution.
delete :: (Typeable a, Show a, Eq a, Ord a, Substitutable a) =>
          a -> Substitution -> Substitution
delete k s = M.update delK (typeOf k) s
    where
      delK (S m) = case (cast m) :: Typeable a => Maybe (Map a a) of
                      Just m' -> let m'' = (M.delete k m')
                                 in if M.null m'' then Nothing
                                    else (Just . S) m''
                      _       -> error "Corrupt substitution."


-- | Lookup a mapping in a substitution based on a given key.
lkup :: (Typeable a, Show a, Eq a, Ord a, Substitutable a) =>
        a -> Substitution -> Maybe a
lkup k s = 
    case M.lookup (typeOf k) s of
      Just (S m) -> case (cast m) :: Typeable a => Maybe (M.Map a a) of
                      Just m' -> M.lookup k m'
                      Nothing -> error "Corrupt substitution"
      Nothing -> Nothing


-- | Domain filtered for all elements of a specific type.
dom :: (Typeable a, Show a, Eq a, Ord a, Substitutable a) =>
       Substitution -> [a]
dom s = M.foldr collect [] s
    where
      collect (S m) l = case (cast m) :: Typeable a => Maybe (Map a a) of
                          Just m' -> l ++ M.keys m'
                          Nothing -> l


-- | Range (co-domain) filtered for all elements of a specific type.
ran :: (Typeable a, Show a, Eq a, Ord a, Substitutable a) =>
       Substitution -> [a]
ran s = M.foldr collect [] s
    where
      collect (S m) l = case (cast m) :: Typeable a => Maybe (Map a a) of
                          Just m' -> l ++ M.elems m'
                          Nothing -> l


-- | Apply a 'Substitution' to an element @x@. If a substitution
-- ranging over the element's type exists in the underlying list, this
-- substitution will be applied to @x@. Otherwise @x@ won't be
-- changed.
app :: (Typeable a, Ord a) => Substitution -> a -> a
app s x = maybe x (.@. x) (M.lookup (typeOf x) s)
    where
      (S m) .@. x = case (cast m) :: Typeable a => Maybe (Map a a) of
                      Just m' -> maybe x id (M.lookup x m')
                      Nothing -> error "Corrupt substitution."


-- | See '.*.'
compose :: Substitution -> Substitution -> Substitution
compose = M.unionWith comp
    where
      (S (o :: M.Map a a)) `comp` (S p) =
          case (cast p) :: Typeable a => Maybe (M.Map a a) of
            Just p' -> S (o .*. p')
            Nothing -> error "Illegal composition."

      o .*. p = (o `without` M.keys p) `M.union` M.map (o .@.) p
      o `without` p = L.foldl (flip M.delete) o p
      o .@. x = apply (fromMap o) x



-- ###################################################################
--      `Substitutable' instance declarations for common types
-- ###################################################################

instance Substitutable ()    ; instance Substitutable Ordering
instance Substitutable Char  ; instance Substitutable Bool
instance Substitutable Int   ; instance Substitutable Integer
instance Substitutable Float ; instance Substitutable Double


instance Substitutable a => Substitutable [a] where
    apply o ls = map (apply o) ls


instance (Show a, Substitutable a) => Substitutable (Maybe a) where
    apply o x = maybe (maybe Nothing (Just . apply o) x) id (lkup x o)


instance (Show a, Show b, Substitutable a,
          Substitutable b) => Substitutable (Either a b) where
    apply o e = maybe (either (Left . apply o) (Right . apply o) e)
                      id (lkup e o)


instance (Show a, Ord a,
          Substitutable a) => Substitutable (Data.Set.Set a) where
    apply o s = maybe (Data.Set.map (apply o) s) id (lkup s o)


instance (Show a, Substitutable a) =>
         Substitutable (Data.Sequence.Seq a) where
             apply o s = maybe (fmap (apply o) s) id (lkup s o)


instance (Substitutable a,
          Substitutable b) => Substitutable (a,b) where
    apply o (x,y) = (o .@. x, o .@. y)


instance (Substitutable a,
          Substitutable b,
          Substitutable c) => Substitutable (a,b,c) where
    apply o (x,y,z) = (o .@. x, o .@. y, o .@. z)


instance (Substitutable a, Substitutable b,
          Substitutable c, Substitutable d) =>
         Substitutable (a,b,c,d) where
             apply o (w,x,y,z) = (o .@. w, o .@. x,
                                  o .@. y, o .@. z)


instance (Substitutable a, Substitutable b,
          Substitutable c, Substitutable d,
          Substitutable e) => Substitutable (a,b,c,d,e) where
    apply o (v,w,x,y,z) = (o .@. v, o .@. w,
                           o .@. x, o .@. y, o .@. z)


instance (Substitutable a, Substitutable b,
          Substitutable c, Substitutable d,
          Substitutable e, Substitutable f) =>
         Substitutable (a,b,c,d,e,f) where
    apply o (u,v,w,x,y,z) = (o .@. u, o .@. v, o .@. w,
                             o .@. x, o .@. y, o .@. z)


instance (Substitutable a, Substitutable b,
          Substitutable c, Substitutable d,
          Substitutable e, Substitutable f,
          Substitutable g) => Substitutable (a,b,c,d,e,f,g) where
    apply o (t,u,v,w,x,y,z) = (o .@. t, o .@. u, o .@. v,
                               o .@. w, o .@. x, o .@. y, o .@. z)



-- ###################################################################
-- Derive `Substitutable` instance declarations using Template Haskell
-- ###################################################################

-- | Derive 'Substitutable' instance definitions for data type and
-- newtype declarations.
deriveSubstitutable :: Name -> Q [Dec]
deriveSubstitutable t = deriveInstDec t mkInstDec
    where
      -- build 'Substitutable' instance declaration
      mkInstDec _ name tvs cs = do
          applyBody <- mapM mkApplyCl cs
          let ty  = mkType (ConT name) tvs
              ctx = buildCtx ''Substitutable tvs ++
                    buildCtx ''Show tvs -- Show is needed for lkup
          return [InstanceD ctx (AppT (ConT ''Substitutable) ty)
                                [FunD (mkName "apply") applyBody]]

      -- TH versions of needed functions and variables
      apply = varE (mkName "apply")
      lkup  = varE (mkName "lkup")
      
      -- build function clause for a constructor
      mkApplyCl (NormalC c fs)  = mkClause c (length fs)
      mkApplyCl (RecC c fs)     = mkClause c (length fs)
      mkApplyCl (InfixC _ c _)  = mkClause c 2

      -- build 'apply' clause for a regular constructor, e.g.,
      -- o .@. x@(C a b) = case lkup x o of
      --                     Just y  -> y
      --                     Nothing -> C (o .@. a) (o .@. b)
      mkClause c n = do
          (pts,vs) <- genPE n
          let x  = mkName "e" -- NOTE: Using the name 'x' brakes the
                              -- code in GHC 7.4 for unknown reasons,
                              -- so we use 'e' as a workaround
                              -- instead. Spooky Template Haskell
                              -- bug...

              y  = mkName "y"
              o  = mkName "o"
          clause [varP o, asP x (conP c pts)]
                 (normalB (caseE (appE (appE lkup (varE x)) (varE o))
                                 [match (conP 'Just [varP y])
                                        (normalB (varE y)) [],
                                  match (conP 'Nothing [])
                                        (normalB (mkConApp
                                                  (conE c) vs
                                                  (appE apply (varE o))
                                                 )
                                        ) []
                                 ])
                 ) []



-- ###################################################################
--           Fresh name generators for variables and types                          
-- ###################################################################
nameSupply  = unsafePerformIO (newMVar 0)

inc s = do n <- readMVar s
           swapMVar s (n+1)

-- | Supplies a fresh name with the given prefix.
-- Note: uses @unsafePerformIO@ internally
freshName :: String -> String
freshName x = x ++ (show $ unsafePerformIO (inc nameSupply))
