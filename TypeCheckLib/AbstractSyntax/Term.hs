{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.AbstractSyntax.Term
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The library's default abstract syntax for terms.
----------------------------------------------------------------------
module TypeCheckLib.AbstractSyntax.Term ( -- * Tags and Terms
                                          Tag (..),
                                          Term (..),
                                          -- * Unification of terms
                                          unifyT,
                                          unifyTs,
                                          -- * Pretty printing
                                          ppT,
                                          t2doc ) where

import TypeCheckLib.AbstractSyntax
import TypeCheckLib.Type
import TypeCheckLib.Evaluable
import TypeCheckLib.Substitution
import TypeCheckLib.Unification
import TypeCheckLib.Instantiation
import TypeCheckLib.Vars

import qualified Text.PrettyPrint as PP
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Foldable (elem)
import Prelude hiding (elem)
import Data.Typeable

-- ###################################################################
--                              Terms
-- ###################################################################

-- | Simple tag implementation providing constant based tags.
data Tag = Let                   -- ^ Let binding
         | LetRec                -- ^ Recursive let binding
         | App                   -- ^ Application
         | Abs                   -- ^ Lambda abstraction
         | IfThenElse            -- ^ Conditional
         | Fix                   -- ^ Fixpoint combinator
         | Tuple                 -- ^ n-ary tuple
         | Head                  -- ^ Method/constructor head
         | Body                  -- ^ Method/constructor body
         | Seq                   -- ^ Sequential composition
         | Return                -- ^ Return statement
         | Invoke                -- ^ Method/field invocation
         | Assign                -- ^ Assignment
         | Cast                  -- ^ Cast
         | Extends               -- ^ Class inheritance
         | Tag String            -- ^ 'String'-based tag
           deriving (Show, Eq, Ord, Typeable)

instance Evaluable Tag
instance Substitutable Tag
instance Instantiable Tag

instance Vars Tag where
    fv = const Set.empty
    bv = const Set.empty
    vs = const Set.empty



-- | Terms are represented by identifiers (variables), constants,
-- object-level binder over terms and n-ary, tagged combiner over
-- terms. Additionally this data structure provides according meta
-- level pendants to be able to use these terms in deduction rules as
-- well as constructors for sequences over terms, sets over terms and
-- meta level function calls evaluating to a term.
data Term = Nil                     -- ^ Empty term
          | Var    Ide              -- ^ Variable
          | Const  Integer          -- ^ Constant
          | Char   Char             -- ^ Character
          | Bind   Ide Term         -- ^ Object level binder
          | K      Tag Int [Term]   -- ^ Tagged combiner over n terms
          | TSeq   (Sequence Term)  -- ^ Sequence of terms
          | TSet   (Set Term)       -- ^ Set of terms
          | TFun   (MetaFun Term)   -- ^ Function evaluating to a term
          | MConst String           -- ^ Meta level constant
          | MChar  String           -- ^ Meta level character
          | MTerm  String           -- ^ Meta level term
            deriving (Show, Eq, Ord, Typeable)


instance AST Term where
    index (MConst id)   n = MConst (id ++ show n)
    index (MChar id)    n = MChar (id ++ show n)
    index (MTerm id)    n = MTerm (id ++ show n)
    index (Var ide)     n = Var (index ide n)
    index (Bind ide t)  n = Bind (index ide n) (index t n)
    index (K tag m ts)  n = K tag m (indexM ts n)
    index (TSeq s)      n = TSeq (indexM s n)
    index (TSet s)      n = TSet (indexM s n)
    index (TFun f)      n = TFun (indexM f n)
    index t             _ = t

    (MTerm _)   ~= t | isMeta t  = False
                     | otherwise = True
    (MConst _)  ~= (Const _)  = True
    (MChar _)   ~= (Char _)   = True
    _           ~= _          = False

    isMeta (MConst _)  = True
    isMeta (MChar _)   = True
    isMeta (MTerm _)   = True
    isMeta _           = False
    

$(deriveEvaluable ''Term)

$(deriveSubstitutable ''Term)

$(deriveInstantiable ''Term)

$(deriveVars ''Term)


-- ###################################################################
--                        Unification of terms
-- ###################################################################

instance Unifiable Term where
    -- Unification of terms
    unify t1 t2 | t1 == t2         = (True, empty)
                | t1 `occursIn` t2 = (False, empty)
                | t2 `occursIn` t1 = (False, empty)
                | otherwise        = unifyT t1 t2

    -- Occurs check
    t `occursIn` (Bind _ t') = t `occursIn` t'
    t `occursIn` (K _ _ ts)  = foldr ((||) . (occursIn t)) False ts
    t `occursIn` (TSeq (ObjSeq s)) = elem t s
    t `occursIn` (TSet (ObjSet s)) = elem t s
    t `occursIn` t' | t == t'   = True
                    | otherwise = False


-- | Unification of terms.
unifyT :: Term -> Term -> (Bool, Substitution)

-- unification of variables
unifyT (Var ide1) (Var ide2) = unify ide1 ide2

-- unification of constants
unifyT var@(MConst _) n@(Const _) = (True, singleton var n)
unifyT n@(Const _) var@(MConst _) = unifyT var n

unifyT v@(MConst _) w@(MConst _) = (True, singleton v w)
unifyT (Const m) (Const n) | m == n    = (True, empty)
                           | otherwise = (False, empty)

-- unification of characters
unifyT mc@(MChar _) c@(Char _) = (True, singleton mc c)
unifyT c@(Char _) mc@(MChar _)  = unifyT mc c

unifyT v@(MChar _) w@(MChar _) = (True, singleton v w)
unifyT (Char c) (Char d) | c == d    = (True, empty)
                         | otherwise = (False, empty)

-- unification of the empty term (nil)
unifyT t Nil = case t of
                 Nil     -> (True, empty)
                 MTerm _ -> (True, singleton t Nil)
                 _       -> (False, empty)
unifyT Nil t = unifyT t Nil

-- unification of meta terms and terms
unifyT m@(MTerm _) t = (True, singleton m t)
unifyT t m@(MTerm _) = unifyT m t

-- unification of binders
unifyT (Bind ide1 t1) (Bind ide2 t2) = unify ide1 ide2 `combine`
                                       unify t1 t2

-- unification of combiners
unifyT (K tag1 _ ts1) (K tag2 _ ts2) | tag1 == tag2 = unifyTs ts1 ts2
                                     | otherwise    = (False, empty)

-- unification of meta and object level term sequences
unifyT (TSeq s1) (TSeq s2) = unify s1 s2

-- unification of meta level sequences and sequential composed terms
unifyT s@(TSeq _) t@(K Seq _ _) = unifyT s (asSeq t)
unifyT t@(K Seq _ _) s@(TSeq _) = unifyT s t

-- unification of meta and object level term sets
unifyT (TSet s1) (TSet s2) = unify s1 s2

-- unification of meta level sets and sequential composed terms
unifyT s@(TSet _) t@(K Seq 2 _) = unifyT s (asSet t)
unifyT t@(K Seq 2 _) s@(TSet _) = unifyT s t

-- In all other cases the two terms are not unifiable.
unifyT _ _ = (False, empty)



-- | Unification of two term lists.
unifyTs :: [Term] -> [Term] -> (Bool, Substitution)
unifyTs [] [] = (True, empty)
unifyTs _  [] = (False, empty)
unifyTs [] _  = (False, empty)
unifyTs ts1 ts2@((TSeq _):_) = unifyTs ts2 ts1
unifyTs ts1 ts2@((TSet _):_) = unifyTs ts2 ts1
unifyTs (x:xs) (y:ys) = let n        = length (y:ys) - length xs
                            (ys',zs) = splitAt n (y:ys)
                            seq      = TSeq (seqFromList ys')
                            set      = TSet (setFromList ys')
                        in case x of
                             TSeq _ -> unifyT x seq `combine`
                                       unifyTs xs zs
                             TSet _ -> unifyT x set `combine`
                                       unifyTs xs zs
                             _      -> unifyT x y `combine`
                                       unifyTs xs ys



-- | Convert sequential composed terms to a list of terms.
asList :: Term -> [Term]
asList (K Seq 2 [t,t']) = t : (asList t')
asList t                = [t]


-- | Convert sequential composed terms to a sequence of terms.
asSeq :: Term -> Term
asSeq t@(K Seq _ _) = TSeq (ObjSeq (Seq.fromList (asList t)))


-- | Convert sequential composed terms to a set of terms.
asSet :: Term -> Term
asSet t@(K Seq _ _) = TSet (ObjSet (Set.fromList (asList t)))



-- ###################################################################
--                      Pretty printer for Terms
-- ###################################################################

-- | Pretty printer for 'Term's.
ppT :: Term -> String
ppT =  PP.render . t2doc

t2doc :: Term -> PP.Doc
t2doc (Nil)        = PP.text "Nil"
t2doc (Var ide)    = PP.text (pprint ide)
t2doc (Const n)    = PP.integer n
t2doc (Char c)     = PP.char c
t2doc (MConst id)  = PP.text id
t2doc (MChar id)   = PP.text id
t2doc (MTerm id)   = PP.text id
t2doc (Bind ide t) = PP.text (pprint ide) PP.<+>
                     PP.text "<-" PP.<+> t2doc t
t2doc (K tag n ts) = PP.brackets (PP.text (show tag) PP.<>
                                  PP.comma PP.<> PP.int n)
                     PP.$$ PP.nest 4 (PP.vcat (map t2doc ts))
t2doc (TSeq seq)   = PP.text (show seq)
t2doc (TSet set)   = PP.text (show set)
t2doc (TFun mf)    = PP.text (pprint mf)