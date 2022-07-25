----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.AssocList
-- Copyright   :  (c) 2010-2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Basic implementation for association lists. This module provides a
-- subset of the 'Data.Map' interface.
----------------------------------------------------------------------
module TypeCheckLib.AssocList ( -- * Query
                                TypeCheckLib.AssocList.null
                              , size
                              , L.lookup
                                -- * Construction
                              , empty
                              , singleton
                                -- * Insertion
                              , insert
                              , insertWith
                                -- * Delete/Update
                              , delete
                              , update
                                -- * Union
                              , unionWith
                                -- * Conversion
                              , elems
                              , keys
                                -- * Folds
                              , TypeCheckLib.AssocList.foldr
                              ) where

import qualified Data.List as L
import qualified Data.Map as M
import Data.Typeable


-- ###################################################################
--                         Association Lists
-- ###################################################################

-- | Is the association list empty?
null :: [(k,a)] -> Bool
null = L.null


-- | The number of elements in the association list.
size :: [(k,a)] -> Int
size = length


-- | The empty association list.
empty :: [(k,a)]
empty = []


-- | An association list with a single element.
singleton :: k -> a -> [(k,a)]
singleton k v = [(k,v)]


-- | Insert a new key and value in the association list.
-- If the key is already present in the list, the associated value is
-- replaced with the supplied value. 'insert' is equivalent to
-- @'insertWith' 'const'@.
insert :: Eq k => k -> a -> [(k,a)] -> [(k,a)]
insert k v [] = [(k, v)]
insert k v (a:as) | fst a == k = (k,v) : as
                  | otherwise  = a : insert k v as


-- | Insert with a function, combining new value and old value.
-- @'insertWith' f key value al@ will insert the pair (key, value)
-- into @al@ if key does not exist in the list. If the key does exist,
-- the function will insert the pair @(key, f new_value old_value)@.
insertWith :: Eq k => (a -> a -> a) -> k -> a -> [(k,a)] -> [(k,a)]
insertWith _ k v [] = [(k, v)]
insertWith f k v (a:as) | fst a == k = (k,f v (snd a)) : as
                        | otherwise  = a : insertWith f k v as


-- | Delete all (key, value) pairs from the given list where the key
-- matches the given one.
delete :: Eq k => k -> [(k,a)] -> [(k,a)]
delete k [] = []
delete k (a:as) | fst a == k = delete k as
                | otherwise  = a : delete k as


-- | The expression (@'update' f k list@) updates the value @x@ at @k@
-- (if it is in the list). If (@f x@) is 'Nothing', the element is
-- deleted. If it is (@'Just' y@), the key @k@ is bound to the new
-- value @y@.
update :: Eq k => (a -> Maybe a) -> k -> [(k,a)] -> [(k,a)]
update _ k [] = []
update f k (a:as) | fst a == k = case f (snd a) of
                                   Just v  -> (k,v) : as
                                   Nothing -> as
                  | otherwise  = a : update f k as


-- | Combine two association lists. If a key is contained in both
-- lists, the values will be combined by the given function.
unionWith :: Eq a => (b -> b -> b) -> [(a,b)] -> [(a,b)] -> [(a,b)]
unionWith _ [] alist = alist
unionWith _ alist [] = alist
unionWith c ((k,v1):as) as2 =
    case L.lookup k as2 of
      Just v2 -> (k, c v1 v2) : unionWith c as (delete k as2)
      Nothing -> (k,v1) : unionWith c as as2


-- | Return all elements of the association list.
elems :: [(k,a)] -> [a]
elems = map snd


-- | Return all keys of the association list.
keys :: [(k,a)] -> [k]
keys = map fst


-- | Fold the values in the map using the given right-associative
-- binary operator, such that @'foldr' f z == 'Prelude.foldr' f z
-- . 'elems'@.
foldr :: (a -> b -> b) -> b -> [(k,a)] -> b
foldr f z as = L.foldr (f . snd) z as