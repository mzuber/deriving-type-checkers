{-# LANGUAGE DeriveDataTypeable, ExistentialQuantification,
             FlexibleInstances #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.AbstractSyntax
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
-- 
-- This modules provides common functionality for defining abstract
-- syntax to be used in deduction rules, e.g., identifier, sets and
-- sequences at meta and object level. Additionally, a mechanism for
-- embedding Haskell functions in deduction rules is provided.
----------------------------------------------------------------------
module TypeCheckLib.AbstractSyntax ( -- * Abstract Syntax
                                     AST (..)
                                     -- * Identifiers
                                   , Identifier (..)
                                   , Ide
                                     -- * Sequences
                                   , ISet (..)
                                   , Sequence (..)
                                   , emptySeq
                                   , seqFromList
                                   , mseq
                                     -- * Sets
                                   , Set (..)
                                   , emptySet
                                   , union
                                   , diff
                                   , (\\)
                                   , setFromList
                                   , setFromSeq
                                   , mset
                                     -- * Meta level functions
                                   , MetaFun (..)
                                     -- * Auxiliary functions
                                   , uncurry3
                                   , uncurry4
                                   , uncurry5
                                   , uncurry6
                                   , uncurry7
                                     -- * Pretty Printing
                                   , PrettyPrint (pprint)
                                   ) where


import TypeCheckLib.Evaluable
import TypeCheckLib.Substitution
import TypeCheckLib.Unification
import TypeCheckLib.Instantiation
import TypeCheckLib.Vars

import Prelude hiding (foldr, and)
import qualified Data.Sequence
import qualified Data.Set
import qualified Data.Map as M
import Data.List (intercalate)
import Data.Maybe
import Data.Typeable
import Data.Functor
import Data.Foldable hiding (elem)


-- ###################################################################
--                         Abstract Syntax
-- ###################################################################

-- | Type class for data structures representing abstract syntax.
-- Minimum complete definition: 'index', '(~=)' and 'isMmeta' or
-- 'index', '(=~)' and 'isMeta'.
class AST a where
    -- | Indexing of meta level elements.
    index  :: a -> Int -> a
    -- | "is meta level pendant of" predicate
    (~=)   :: a -> a -> Bool
    -- | "is object level pendant of" predicate
    (=~)   :: a -> a -> Bool
    -- | Discriminator for meta level elements.
    isMeta :: a -> Bool

    (~=) = flip (=~)
    (=~) = flip (~=)


instance (AST a, AST b) => AST (a,b) where
    index (a,b) n = (index a n, index b n)                
    isMeta (a,b)  = isMeta a && isMeta b
    (a1,b1) ~= (a2,b2) = a1 ~= a2 && b1 ~= b2


instance (AST a, AST b, AST c) => AST (a,b,c) where
    index (a,b,c) n = (index a n, index b n, index c n)                
    isMeta (a,b,c)  = isMeta a && isMeta b && isMeta c
    (a1,b1,c1) ~= (a2,b2,c2) = a1 ~= a2 && b1 ~= b2 && c2 ~= c2


instance (AST a, AST b, AST c, AST d) => AST (a,b,c,d) where
    index (a,b,c,d) n = (index a n, index b n,
                         index c n, index d n)
    isMeta (a,b,c,d)  = isMeta a && isMeta b
                        && isMeta c && isMeta d
    (a1,b1,c1,d1) ~= (a2,b2,c2,d2) = a1 ~= a2 && b1 ~= b2
                                     && c2 ~= c2 && d1 ~= d2


instance (AST a, AST b, AST c, AST d, AST e) => AST (a,b,c,d,e) where
    index (a,b,c,d,e) n = (index a n, index b n,
                           index c n, index d n, index e n)
    isMeta (a,b,c,d,e)  = isMeta a && isMeta b &&
                          isMeta c && isMeta d && isMeta e
    (a1,b1,c1,d1,e1) ~= (a2,b2,c2,d2,e2) =
        a1 ~= a2 && b1 ~= b2 && c2 ~= c2 && d1 ~= d2 && e1 ~= e2


instance (AST a, AST b, AST c,
          AST d, AST e, AST f) => AST (a,b,c,d,e,f) where
    index (a,b,c,d,e,f) n = (index a n, index b n, index c n,
                             index d n, index e n, index f n)
    isMeta (a,b,c,d,e,f)  = isMeta a && isMeta b && isMeta c
                            && isMeta d && isMeta e && isMeta f
    (a1,b1,c1,d1,e1,f1) ~= (a2,b2,c2,d2,e2,f2) =
        a1 ~= a2 && b1 ~= b2 && c2 ~= c2 &&
        d1 ~= d2 && e1 ~= e2 && f1 ~= f2


instance (AST a, AST b, AST c,
          AST d, AST e, AST f, AST g) => AST (a,b,c,d,e,f,g) where
    index (a,b,c,d,e,f,g) n = (index a n, index b n, index c n,
                               index d n, index e n, index f n,
                               index g n)
    isMeta (a,b,c,d,e,f,g)  = isMeta a && isMeta b && isMeta c
                              && isMeta d && isMeta e && isMeta f
                              && isMeta g
    (a1,b1,c1,d1,e1,f1,g1) ~= (a2,b2,c2,d2,e2,f2,g2) =
        a1 ~= a2 && b1 ~= b2 && c2 ~= c2 &&
        d1 ~= d2 && e1 ~= e2 && f1 ~= f2 && g1 ~= g2


instance AST a => AST [a] where
    index xs n = map ((flip index) n) xs
    isMeta     = foldr ((&&) . isMeta) True
    xs ~= ys   = and (zipWith (~=) xs ys)



-- ###################################################################
--                            Identifiers
-- ###################################################################

-- | Object and meta level identifiers for use in deduction rules.
data Identifier a = MIde String       -- ^ Meta level identifier
                  | Ide  a            -- ^ Object level identifier
                    deriving (Show, Eq, Ord, Typeable)

type Ide = Identifier String

instance AST (Identifier a) where
    index (MIde id) n = MIde (id ++ show n)
    index id        _ = id

    (MIde _) ~= (Ide _) = True
    _        ~= _       = False

    isMeta (MIde _) = True
    isMeta (Ide _)  = False

instance Evaluable (Identifier a) where
    isEvaluable (MIde _) = False
    isEvaluable (Ide _)  = True

instance (Typeable a, Ord a) => Substitutable (Identifier a)

instance (Typeable a, Show a, Ord a, Unifiable a) =>
         Unifiable (Identifier a) where
    unify mid@(MIde _) id@(Ide _) = (True, singleton mid id)
    unify id@(Ide _) mid@(MIde _) = unify mid id

    unify (Ide id1)     (Ide id2)     = unify id1 id2
    unify m1@(MIde id1) m2@(MIde id2) = (True, singleton m1 m2)

instance (Typeable a, Eq a) => Instantiable (Identifier a) where
    indexM (MIde id) n = MIde (id ++ show n)
    indexM id        _ = id

instance Vars (Identifier a) where
    fv = const Data.Set.empty
    bv = const Data.Set.empty
    vs = const Data.Set.empty



-- ###################################################################
--                        Sets and Sequences                                     
-- ###################################################################

-- | Object and meta level index sets for use in deduction rules.
data ISet = MetaISet String        -- ^ Meta level index set
          | ISet [Int]             -- ^ Object level index set
            deriving (Show, Eq, Ord, Typeable)

instance Evaluable ISet where
    isEvaluable (MetaISet t) = False
    isEvaluable (ISet _)     = True

instance Substitutable ISet


----------------------------------------------------------------------


-- | Object and meta level sequences for use in deduction rules.
data Sequence a = MetaSeq ISet a                -- ^ Meta level sequence.
                | ObjSeq (Data.Sequence.Seq a)  -- ^ Object level sequence.
                  deriving (Show, Eq, Ord, Typeable)


instance (AST a, Instantiable a,
          Substitutable a) => AST (Sequence a) where
    index = indexM

    (MetaSeq _ _) ~= (ObjSeq _) = True
    _             ~= _          = False

    isMeta (MetaSeq _ _) = True
    isMeta _             = False


instance Evaluable a => Evaluable (Sequence a) where
    isEvaluable (MetaSeq _ _) = False
    isEvaluable (ObjSeq s)    = True

    eval (ObjSeq s)       = ObjSeq (fmap eval s)
    eval ms@(MetaSeq _ _) = ms


instance (Show a, Substitutable a) =>
         Substitutable (Sequence a) where
    apply o (ObjSeq s)    = ObjSeq (apply o s)
    apply o (MetaSeq i x) = MetaSeq (apply o i) x


instance (Substitutable a, Unifiable a,
          Instantiable a) => Unifiable (Sequence a) where
    unify (MetaSeq mi@(MetaISet _) x) (ObjSeq s) =
        let s'    = toList s
            n     = length s'
            xs    = map (indexM x) [1..n]
            (b,o) = unify xs s'
            p     = singleton mi (ISet [1..n])
        in if b then (True, o .*. p)
           else (False, empty)
    unify s@(ObjSeq _) ms@(MetaSeq mi@(MetaISet _) x) = unify ms s

    unify (ObjSeq s1) (ObjSeq s2)     = unify s1 s2
    unify (MetaSeq _ _) (MetaSeq _ _) = (False, empty)


instance (Substitutable a,
          Instantiable a) => Instantiable (Sequence a) where
    unfold (ObjSeq s)           = ObjSeq (unfold s)
    unfold (MetaSeq (ISet i) x) = ObjSeq (Data.Sequence.fromList s)
        where
          s = take (length i) (zipWith indexM (repeat x) i)
    unfold m@(MetaSeq (MetaISet _) _) = m

    indexM (ObjSeq s) n = ObjSeq (fmap ((flip indexM) n) s)
    indexM s          _ = s

    instMT (ObjSeq s) = instMT s
    instMT s          = return empty


instance Vars a => Vars (Sequence a) where
    fv (ObjSeq s) = fv s
    fv _          = Data.Set.empty

    bv (ObjSeq s) = bv s
    bv _          = Data.Set.empty

    vs (ObjSeq s) = vs s
    vs _          = Data.Set.empty


-- | Empty object level sequence.
emptySeq :: Sequence a
emptySeq = ObjSeq (Data.Sequence.empty)


-- | Build object level sequence from a given list.
seqFromList :: [a] -> Sequence a
seqFromList = ObjSeq . Data.Sequence.fromList


-- | Convenience function for buildung meta level seqs.
mseq :: String -> a -> Sequence a
mseq i a = MetaSeq (MetaISet i) a


----------------------------------------------------------------------


-- | Object and meta level sets for use in deduction rules.
data Set a = MetaSet ISet a                 -- ^ Meta level set.
           | ObjSet (Data.Set.Set a)        -- ^ Object level set.
           | SetFun (MetaFun (Set a))       -- ^ Meta level function
                                            --   evaluating to a set.
             deriving (Show, Eq, Ord, Typeable)


instance (Ord a, AST a, Instantiable a,
          Substitutable a) => AST (Set a) where
    index = indexM

    (MetaSet _ _) ~= (ObjSet _) = True
    _             ~= _          = False

    isMeta (MetaSet _ _) = True
    isMeta _             = False


instance (Evaluable a, Ord a) => Evaluable (Set a) where
    isEvaluable (MetaSet _ _) = False
    isEvaluable (ObjSet s)    = True
    isEvaluable (SetFun f)    = isEvaluable f

    eval (ObjSet s)       = ObjSet (eval s)
    eval ms@(MetaSet _ _) = ms
    eval s@(SetFun (MF id f args)) | isEvaluable args =
                                       fromMaybe s (f (eval args))
                                   | otherwise        = s

    isMF (SetFun _) = True
    isMF (ObjSet s) = isMF s
    isMF _          = False


instance (Show a, Ord a, Substitutable a) =>
         Substitutable (Set a) where
    apply o (ObjSet s)    = ObjSet (apply o s)
    apply o (MetaSet i x) = MetaSet (apply o i) x
    apply o (SetFun f)    = SetFun (apply o f)


instance (Substitutable a, Unifiable a,
          Instantiable a) => Unifiable (Set a) where
    unify (MetaSet mi@(MetaISet _) x) (ObjSet s) =
        let s' = toList s
            n  = length s'
            xs = map (indexM x) [1..n]
            (b,o) = unify xs s'
            p = singleton mi (ISet [1..n])
        in if b then (True, o .*. p)
           else (False, empty)
    unify s@(ObjSet _) ms@(MetaSet mi@(MetaISet _) x) = unify ms s

    unify (ObjSet s1) (ObjSet s2) = unify s1 s2
    unify _ _                     = (False, empty)


instance (Ord a, Substitutable a,
          Instantiable a) => Instantiable (Set a) where
    unfold (ObjSet s)           = ObjSet (unfold s)
    unfold (MetaSet (ISet i) x) = ObjSet (Data.Set.fromList s)
        where
          s = take (length i) (zipWith indexM (repeat x) i)
    unfold m@(MetaSet (MetaISet _) _) = m
    unfold (SetFun f)                 = SetFun (unfold f)

    indexM (ObjSet s) n = ObjSet (Data.Set.map ((flip indexM) n) s)
    indexM (SetFun f) n = SetFun (indexM f n)
    indexM s          _ = s

    instMT (ObjSet s) = instMT s
    instMT (SetFun f) = instMT f
    instMT s          = return empty


instance Vars a => Vars (Set a) where
    fv (ObjSet s) = fv s
    fv _          = Data.Set.empty

    bv (ObjSet s) = bv s
    bv _          = Data.Set.empty

    vs (ObjSet s) = vs s
    vs _          = Data.Set.empty


-- | Empty object level set.
emptySet :: Set a
emptySet = ObjSet (Data.Set.empty)


-- | Union of object level sets.
union :: Ord a => Set a -> Set a -> Maybe (Set a)
(ObjSet s) `union` (ObjSet s') = Just (ObjSet (Data.Set.union s s'))
_          `union` _           = Nothing


-- | Difference of object level sets
diff :: Ord a => Set a -> Set a -> Maybe (Set a)
diff (ObjSet s) (ObjSet s') = Just (ObjSet (Data.Set.difference s s'))
diff _          _           = Nothing


-- | Meta level version of 'diff'.
(\\) :: ( Ord a, PrettyPrint a, Evaluable a,
          Instantiable a, Substitutable a, Vars a ) =>
        Set a -> Set a -> Set a
s1 \\ s2 = SetFun (MF "diff" (uncurry diff) (s1,s2))


-- | Build object level set from a given list.
setFromList :: Ord a => [a] -> Set a
setFromList = ObjSet . Data.Set.fromList


-- | Build set from a given sequence.
setFromSeq :: Ord a => Sequence a -> Set a
setFromSeq (ObjSeq s)       = ObjSet (Data.Set.fromList (toList s))
setFromSeq (MetaSeq iset a) = MetaSet iset a


-- | Convenience function for buildung meta level sets.
mset :: String -> a -> Set a
mset i a = MetaSet (MetaISet i) a



-- ###################################################################
--                         Meta Level Functions                                   
-- ###################################################################

-- | Meta level wrapper for auxiliary function calls in deduction
-- rules.  Functions with more than one argument need to be uncurried
-- to be wrapped up in this data structure.
data MetaFun b = forall a . (Show a, Evaluable a, Substitutable a,
                             Instantiable a, PrettyPrint a, Vars a) =>
                            MF String (a -> Maybe b) a
                            deriving (Typeable)


instance Show (MetaFun b) where
    show (MF id _ args) = id ++ " " ++ show args

instance Eq (MetaFun b) where
    (MF id1 _ _) == (MF id2 _ _) = id1 == id2

instance Ord (MetaFun b) where
    (MF id1 _ _) < (MF id2 _ _) = id1 < id2

instance Evaluable (MetaFun b) where
    isEvaluable (MF _ f x) | isEvaluable x = isJust (f (eval x))
                           | otherwise     = False
    isMF = const True

instance Typeable b => Substitutable (MetaFun b) where
    apply o (MF id f x) = MF id f (apply o x)

instance Typeable b => Instantiable (MetaFun b) where
    unfold (MF id f x)   = MF id f (unfold x)
    indexM (MF id f x) n = MF id f (indexM x n)
    instMT (MF _ _ x)    = instMT x

instance Vars (MetaFun b) where
    fv (MF _ _ x) = fv x
    bv (MF _ _ x) = bv x
    vs (MF _ _ x) = vs x



-- ###################################################################
--                          Auxiliary Functions                                   
-- ###################################################################

-- | Uncurry for functions with three arguments.
uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f = \(x,y,z) -> f x y z


-- | Uncurry for functions with four arguments.
uncurry4 :: (a -> b -> c -> d -> e) -> (a, b, c, d) -> e
uncurry4 f = \(w,x,y,z) -> f w x y z


-- | Uncurry for functions with five arguments.
uncurry5 :: (a -> b -> c -> d -> e -> f) -> (a, b, c, d, e) -> f
uncurry5 f = \(v,w,x,y,z) -> f v w x y z


-- | Uncurry for functions with six arguments.
uncurry6 :: (a -> b -> c -> d -> e -> f -> g) ->
            (a, b, c, d, e, f) -> g
uncurry6 f = \(u,v,w,x,y,z) -> f u v w x y z


-- | Uncurry for functions with seven arguments.
uncurry7 :: (a -> b -> c -> d -> e -> f -> g -> h) ->
            (a, b, c, d, e, f, g) -> h
uncurry7 f = \(t,u,v,w,x,y,z) -> f t u v w x y z



-- ###################################################################
--                          Pretty Printing
-- ###################################################################

-- | Type class providing a pretty printing function used to generate 
-- pretty error messages in the case a constraint could not be solved.
class Show a => PrettyPrint a where
    pprint :: a -> String
    pprint = show


instance PrettyPrint () where
    pprint = const ""


instance PrettyPrint Char where
    pprint c = [c]


instance PrettyPrint [Char] where
    pprint = id


instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (a,b) where
    pprint (x,y) = "(" ++ pprint x ++ ", " ++ pprint y ++ ")"


instance (PrettyPrint a, PrettyPrint b,
          PrettyPrint c) => PrettyPrint (a,b,c) where
    pprint (x,y,z) = "(" ++ pprint x ++ ", " ++ pprint y ++
                     ", " ++ pprint z ++ ")"


instance (PrettyPrint a, PrettyPrint b,
          PrettyPrint c, PrettyPrint d) => PrettyPrint (a,b,c,d) where
    pprint (w,x,y,z) = "(" ++ pprint w ++ ", " ++ pprint x ++
                       ", " ++ pprint y ++ ", " ++ pprint z ++ ")"


instance (PrettyPrint a, PrettyPrint b,
          PrettyPrint c, PrettyPrint d,
          PrettyPrint e) => PrettyPrint (a,b,c,d,e) where
    pprint (v,w,x,y,z) = "(" ++ pprint v ++ ", " ++ pprint w ++
                         ", " ++ pprint x ++ ", " ++ pprint y ++ 
                         ", " ++ pprint z ++ ")"


instance (PrettyPrint a, PrettyPrint b, PrettyPrint c,
          PrettyPrint d, PrettyPrint e, PrettyPrint f) =>
         PrettyPrint (a,b,c,d,e,f) where
    pprint (u,v,w,x,y,z) = "(" ++ pprint u ++ ", " ++ pprint v ++
                           ", " ++ pprint w ++ ", " ++ pprint x ++ 
                           ", " ++ pprint y ++ ", " ++ pprint z ++ ")"


instance (PrettyPrint a, PrettyPrint b, PrettyPrint c,
          PrettyPrint d, PrettyPrint e, PrettyPrint f,
          PrettyPrint g) => PrettyPrint (a,b,c,d,e,f,g) where
    pprint (t,u,v,w,x,y,z) = "(" ++ pprint t ++ ", " ++ pprint u ++
                             ", " ++ pprint v ++ ", " ++ pprint w ++ 
                             ", " ++ pprint x ++ ", " ++ pprint y ++
                             ", " ++ pprint z ++ ")"


instance PrettyPrint a => PrettyPrint (Maybe a) where
    pprint (Just x) = pprint x
    pprint Nothing  = "Nothing"


instance (PrettyPrint a, PrettyPrint b) =>
         PrettyPrint (Either a b) where
    pprint = either pprint pprint


instance PrettyPrint a => PrettyPrint (Identifier a) where
    pprint (Ide ide)  = pprint ide
    pprint (MIde ide) = ide


instance PrettyPrint ISet where
    pprint (MetaISet id) = id
    pprint (ISet s)      = "{" ++ intercalate ", " (map show s) ++ "}"


instance PrettyPrint a => PrettyPrint (Data.Sequence.Seq a) where
    pprint s = "<" ++ intercalate ", " (map pprint (toList s)) ++ ">"


instance PrettyPrint a => PrettyPrint (Sequence a) where
    pprint (MetaSeq iset a) = "/\\ " ++ pprint iset ++
                              " (" ++ pprint a ++ ")"
    pprint (ObjSeq s)       = pprint s


instance PrettyPrint a => PrettyPrint (Data.Set.Set a) where
    pprint s = "{" ++ intercalate ", " (map pprint (toList s)) ++ "}"


instance PrettyPrint a => PrettyPrint (Set a) where
    pprint (MetaSet iset a) = "U " ++ pprint iset ++
                              " {" ++ pprint a ++ "}"
    pprint (ObjSet s)       = pprint s
    pprint (SetFun f)       = pprint f


instance PrettyPrint (MetaFun b) where
    pprint (MF id _ args) = id ++ pprint args