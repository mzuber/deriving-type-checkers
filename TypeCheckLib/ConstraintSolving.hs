----------------------------------------------------------------------
-- |
-- Module      :  GuiTool.ConstraintSolving
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module provides data structures and functions needed to solve
-- the constraints generated by the library's constraint generation
-- framework.
----------------------------------------------------------------------
module TypeCheckLib.ConstraintSolving ( -- * Constraint solving results
                                   Result (..)
                                 , IntermediateResult (..)
                                   -- * Constraint solver
                                 , solveCs
                                 , solveCsScan
                                 ) where

import TypeCheckLib.AbstractSyntax hiding (union)
import TypeCheckLib.Rule hiding (empty, union, delete)
import TypeCheckLib.Evaluable
import TypeCheckLib.Substitution hiding (delete)
import TypeCheckLib.Unification
import TypeCheckLib.Instantiation
import TypeCheckLib.Vars
import TypeCheckLib.ConstraintGeneration

import Prelude hiding (foldr, null, all)
import Data.Typeable
import Data.Foldable
import Data.List (partition, delete)
import Data.Maybe (fromJust)
import Data.Set (Set, null, intersection, union)


-- ###################################################################
--                         Constraint Solver
-- ###################################################################

-- | Return data type of the library's constraint solving function.
data Result = Success (Substitution)  -- ^ All constraints have been
                                      -- solved and the possibly
                                      -- arisen substitution is
                                      -- returned.
            | NoRuleFound (Judgement) -- ^ No matching rule was found
                                      -- for one of the goals during
                                      -- constraint generation.
            | Failure (Judgement)     -- ^ At least one constraint
                                      -- couldn't be solved. The first
                                      -- unsolvable constraint
                                      -- occurring is returned.
            | PostPone (Judgement)    -- ^ The dissolving of a
                                      -- constraint needs to be
                                      -- deferred.
            | Error    String         -- ^ A non-constraint-related
                                      -- error occurred. Panic!
              deriving Show

-- | Intermediate resulst of the sovling process.
--  Needed for Debuging and stepping through the solving via GUI
data IntermediateResult = IRes {
                            con   :: Judgement,    -- ^ the current constraint to solve
                            res   :: Result,       -- ^ the result to that constraint
                            subs  :: Substitution, -- ^ all collect substitution till now
                            unsolv:: [Judgement]   -- ^ still unsolved constraints
                            }                           
                            deriving Show
emptyIr = IRes {con = Sep 0, res = Error "empty", subs = empty, unsolv = []}

-- | Solve the generated constraints and return the possibly arisen
-- substitution. The function performs a dependency analysis to
-- postpone constraints which contain meta level functions with type
-- variable arguements bound by other constraints.
solveCs :: [Judgement] -> Result
solveCs cs = let (cs', pcs) = partitionCs cs
             in snd $ (solveCs' cs' pcs empty)


-- | Same as solveCs, but returns also the intermediate results
solveCsScan :: [Judgement] -> ([IntermediateResult], Result)
solveCsScan cs = let (cs', pcs) = partitionCs cs
             in solveCs' cs' pcs empty

solveCs' :: [Judgement]   -- ^ Constraints
         -> [Judgement]   -- ^ Postponed constraints
         -> Substitution  -- ^ Unifier found in previous steps
         -> ([IntermediateResult], Result)
solveCs' [] [] mgu      = ([emptyIr{res = Success mgu, subs = mgu}], Success mgu)
solveCs' (c:cs) pcs mgu = let ir = emptyIr {con = c, subs = mgu, unsolv = c:cs ++ pcs}
                          in
                            case solveC c of
                            -- The constraint could have been
                            -- solved. Apply the found substitution to
                            -- the remaining constraints and try to
                            -- solve them.
                            Success o -> let (irs,r) = solveRCs o
                                             ir' = ir{res = Success o}
                                         in (ir':irs, r)
                            -- The constraint is not evaluable,
                            -- thus the dissolving is postponed.
                            PostPone p -> let (irs,r) = solveCs' cs (c:pcs) mgu
                                              ir' = ir{res = PostPone p}
                                          in (ir':irs,r)
                            -- If an error or failure occurred, just
                            -- return it.
                            result -> ([ir{res = result}],result)
    where
      -- Try to solve remaining constraints.
      solveRCs o = let p = o .*. mgu
                   in solveCs' (applyU p cs) (applyU p pcs) p

      -- If c could be solved: apply possibly found unifier to all
      -- remaining constraints, try to unfold meta level sets and
      -- sequences in the remaining constraints and apply found
      -- unifier to the unfolded constraints, too.
      applyU o js = let js' = map (unfold . apply o) js
                    in map (o .@.) js'
      
solveCs' [] pcs@(pc:_) mgu = let (cs,pcs') = partitionCs pcs
                             in if all (not . isEvaluable) cs
                                then ([emptyIr{res = Failure (last pcs), subs = mgu, unsolv = pcs}],
                                       Failure (last pcs))
                                else solveCs' cs pcs' mgu
 


-- | Evaluate possible meta functions in a given constraint and try to
-- solve it.
solveC :: Judgement -> Result
solveC j@(C c) = if isEvaluable c then solve
                 else PostPone j
    where
      solve = let (b,s) = solveC' (eval c)
              in if b then Success s
                 else Failure j

-- Ignore separators and handle judgements for
-- which a matching rule haven't been found:
solveC (NoRule j) = NoRuleFound j
solveC (Sep _)    = Success empty

solveC _ = error "Trying to solve non-constraint judgement."


-- | Solve constraints.
solveC' :: ( Show a, Eq a, Evaluable a, Substitutable a,
             Unifiable a, Instantiable a, PrettyPrint a ) =>
           Constraint a -> (Bool, Substitution)
solveC' (Eq x y _)                   = unify x y
solveC' (Constraint (MF _ f args) _) = fromJust (f args)
solveC' (Predicate (MF _ p x) _)     = (fromJust (p x),empty)

-- solve negations
solveC' (Not c _) = let (b,s) = solveC' c in (not b,s)

-- solve conjunctions
solveC' (And c d err)
    | isEvaluable c = let mgu@(b,s) = solveC' c
                          d'        = (unfold . apply s) d
                      in if isEvaluable d'
                         then combine mgu (solveC' (eval d'))
                         else (False,empty)
    | isEvaluable d = solveC' (And d c err)
    | otherwise     = (False,empty)

-- solve disjunctions
solveC' (Or c d err)
    | isEvaluable c = let mgu1@(b1,s) = solveC' c
                          d'          = (unfold . apply s) d
                          mgu2@(b2,_) = solveC' (eval d')
                      in if isEvaluable d' then 
                             if b1 then
                                 if b2 then combine mgu1 mgu2
                                 else mgu1
                             else
                                 if b2 then mgu2
                                 else (False,empty)
                         else mgu1
    | isEvaluable d = solveC' (Or d c err)
    | otherwise     = (False,empty)

-- solve conditionals
solveC' (If c d _) = let mgu1@(b1,s) = solveC' c
                         d'          = (unfold . apply s) d
                         mgu2@(b2,_) = solveC' (eval d')
                     in if isEvaluable d' then
                            if b1 then
                                if b2 then combine mgu1 mgu2
                                else (False,empty)
                            else (True,empty)
                        else (False,empty)

-- solve constraint sequences
solveC' (ConstraintSeq (ObjSeq s) _) = foldr (combine . solveC')
                                             (True,empty) s



-- | Dependency analysis of the constraint list.
partitionCs :: [Judgement] -> ([Judgement],[Judgement])
partitionCs cs = chkEvaluability (partition depA cs)
    where
      -- check if type variables contained as arguments in a meta
      -- level function are bound by another constraint
      depA c | isMF c = let vars = vs (delete c cs)
                        in null (getVars c `intersection` vars) 
             | otherwise = True

      -- determine type variable arguments of the meta level functions
      -- contained in constraints
      getVars (C (Eq x y _)) | isMF x && isMF y = vs x `union` vs y
                             | isMF x           = vs x
                             | otherwise        = vs y
      getVars (C (And c d _)) | isMF c && isMF d = vs c `union` vs d
                              | isMF c           = vs c
                              | otherwise        = vs d
      getVars (C (Or c d _)) | isMF c && isMF d = vs c `union` vs d
                             | isMF c           = vs c
                             | otherwise        = vs d
      getVars (C (If c b _)) | isMF c && isMF b = vs c `union` vs b
                             | isMF c           = vs c
                             | otherwise        = vs b
      getVars (C c) = vs c

      -- if the dependency analysis yields no independent constraints,
      -- start to solve the constraints which are evaluable anyway
      chkEvaluability ([],_) = partition isEvaluable cs
      chkEvaluability ptn    = ptn