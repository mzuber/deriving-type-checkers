{-# LANGUAGE ScopedTypeVariables, DoAndIfThenElse #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.ConstraintGeneration
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The library's constraint generation framwork: for a given list of
-- 'Rule's and a 'Judgement' representing the current subgoal, the
-- 'genCs' function generates the list of constraints (encapsulated as
-- 'Judgement's).
----------------------------------------------------------------------
module TypeCheckLib.ConstraintGeneration ( genCs, genCsScan ) where

import TypeCheckLib.AbstractSyntax
import TypeCheckLib.Type
import TypeCheckLib.Substitution as S
import TypeCheckLib.Unification
import TypeCheckLib.Instantiation
import TypeCheckLib.Rule

import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
import Control.Monad (liftM)
import Data.Typeable
import Data.Tree

-- | The constraint generation function generates a list of
-- constraints for a given judgement such that the judgement holds if
-- and only if these cosntraints have a solution. The implementation
-- `traverses' the type derivation tree and collects the arisen
-- constraints in a depth-first manner.
genCs :: [Rule]                 -- ^ List of Rules
      -> Judgement              -- ^ The current subgoal
      -> Bool                   -- ^ Debug flag
      -> TypeCheckM [Judgement] -- ^ Constraint list
genCs [] _ dbg = return []
genCs rs j dbg = liftM fst $ genCs' rs rs j dbg 

genCsScan rules j dbg = genCs' rules rules j dbg

genCs' :: [Rule] -> [Rule] -> Judgement -> Bool
       -> TypeCheckM ([Judgement], Tree (Judgement, Maybe Rule))
genCs' _     []               j _   = return ([NoRule j], Node (NoRule j, Nothing ) [])
genCs' rules (rule@(Rule ps c):rs) j dbg = if b then cs
                                      else genCs' rules rs j dbg
    where
      -- Try to instantiate the rule by finding a unifier
      -- between the conclusion and the given judgement.
      (b, s) = instRule c j

      cs = do -- Apply found substitutions to all premises.
              let ps' = map (s .@.) ps
              -- Try to unfold judgement sequences in the premises.
              let unfPs = concatMap asList (map unfold ps')
              -- Apply substitutions to unfolded premises, too.
              let unfPs' = map (s .@.) unfPs

              -- Generate substitution which instantiates all meta
              -- types in the constraint premises with fresh type
              -- variables.
              o <- instMT (filter isC unfPs')
              let s' = s .*. o

              -- Apply the found substitution to all premises.
              let instPs = map (s' .@.) unfPs'

              -- Generate a substitution which instantiates all
              -- remaining meta types in the judgement premises
              -- with fresh type variables.
              p <- instMT $ filter (not . isC) instPs
              let s'' = s' .*. p

              -- Apply this substitution to the constraints.
              let instPs' = map (s'' .@.) instPs

              -- Generate constraints for remaining premises and build
              -- constraint list.  For testing and debugging: add a
              -- seperator indicating which rule had been instantiated
              let sep = Sep $ fromMaybe (-1)
                              (elemIndex (Rule ps c) rules)
              (list, trees) <- mkCList instPs'
              if dbg
              then return (sep:list, Node (j, Just rule) trees)
              else return (list, Node (j, Just rule) trees)

      mkCList [] = return ([],[])
      mkCList (j:js) | isC j     = do (list, trees) <- mkCList js 
                                      return (j:list , Node (j,Nothing) [] : trees) 
                     | otherwise = do (cs1,ts1) <- genCs' rules rules j dbg
                                      (cs2,ts2) <- mkCList js
                                      return (cs1 ++ cs2, ts1:ts2)



-- | Try to instantiate the conclusion of a rule with a given judgement.
instRule :: Judgement -> Judgement -> (Bool, Substitution)
instRule j1@(J c1 (e1 :: a) t1) j2@(J c2 e2 t2) = (b, mgu)
    where
      b   = b1 && b2 && b3
      mgu = if b then s .*. (o .*. p)
            else S.empty

      -- unify contexts
      (b1,s) = unify c1 c2

      -- unify expressions
      (b2,o) = case (cast e2) :: Maybe a of
                 Nothing  -> (False, S.empty)
                 Just e2' -> unify e1 e2'

      -- unify types
      (b3,p) = unify t1 t2

instRule j1 j2 = error "Non-judgement instantiation"
