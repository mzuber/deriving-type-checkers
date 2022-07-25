----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Type
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Bootstrapping file to brake the cycle in the module import graph
-- between 'Instantiation' and 'Type'.
----------------------------------------------------------------------
module TypeCheckLib.Type ( -- * Default types
                           Ty (..)
                           -- ** Auxilary functions on types
                         , (->:)
                         , (×)
                         , (**)
                         , mkT
                         , mkTV
                         , genInstOf
                         , (>=)
                           -- * Type checking monad
                         , TypeCheckM
                         , freshTV
                         , evalTypeCheckM
                         ) where

import TypeCheckLib.Substitution

import Data.Typeable
import Control.Monad.State
import Prelude hiding ((>=), (**), elem)


-- ###################################################################
--                      Default type implementation
-- ###################################################################

-- | Basic type implementation.
data Ty

instance Show Ty
instance Eq Ty
instance Ord Ty
instance Typeable Ty


----------------- Auxiliary functions for default types --------------

-- | Construct function type.
(->:) :: Ty -> Ty -> Ty


-- | Construct binary tuple type (UTF8 version).
-- Note: this is the UTF8 symbol 'times', NOT an x.
(×) :: Ty -> Ty -> Ty


-- | Construct binary tuple type (ASCII version).
(**) :: Ty -> Ty -> Ty


-- | Construct object level base type.
mkT :: String -> Ty


-- | Construct a type variable.
mkTV :: String -> Ty


-- | Check if a type is a generic instance of a given type scheme.
genInstOf :: Ty -> Ty -> Maybe (Bool, Substitution)

-- | Check if a type is a generic instance of a given type scheme
-- (operator version).  The following identity holds: @t1 `genInstOf`
-- t2@ = @t2 >= t1@
(>=) :: Ty -> Ty -> Maybe (Bool, Substitution)



-- ###################################################################
--                          TypeCheck Monad
-- ###################################################################

-- | During constraint generation the need for fresh type variables
-- arises. In order to be able to generate fresh names, the constraint
-- generation algorithm will run in a state monad carrying an unused
-- index.
type TypeCheckM = State Int


-- | Generate a fresh type variable.
freshTV :: TypeCheckM Ty


-- | Evaluate the type check monad.
evalTypeCheckM :: TypeCheckM a -> a
