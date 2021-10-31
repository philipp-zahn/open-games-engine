module Data.Map.Interface

import Data.List
import Data.SortedMap

public export
interface Map (0 m : Type -> Type -> Type) where
  constructor IMap
  ||| The empty map
  empty : m k v

  ||| A map with a single element
  singleton : k -> v -> m k v
  ||| merging two maps and using the provided function to deal with collisions
  mergeWith : Eq k => (v -> v -> v) -> m k v -> m k v -> m k v

  ||| Map keys with possible collisions
  mapKeysWith : Eq k' => (k -> k') -> (v -> v -> v) -> m k v -> m k' v

  ||| Map values of the map
  mapVals : (v -> v') -> m k v -> m k v'

  ||| Lookup a value in the map
  lookup : Eq k => k -> m k v -> Maybe v

export
mapKeys : Map m => Eq k' => Monoid v => (k -> k') -> m k v -> m k' v
mapKeys f = mapKeysWith f (<+>)

export
merge : Map m => Eq k => Monoid v => m k v -> m k v -> m k v
merge = mergeWith (<+>)

public export
LookupList : (k, v : Type) -> Type
LookupList k v = List (k, v)

normaliseWith : Eq k => (v -> v -> v) -> LookupList k v -> LookupList k v
normaliseWith f xs = normaliseAcc xs []
  where
    normaliseAcc : LookupList k v -> LookupList k v -> LookupList k v
    normaliseAcc [] ys = ys
    normaliseAcc (y@(key, val) :: xs) ys = case List.lookup key ys of
                                                Nothing => normaliseAcc xs (y :: ys)
                                                Just val' => normaliseAcc xs ((key, f val val') :: ys)

implementation Map LookupList where
  empty = []
  singleton k v = pure (k, v)
  mergeWith f = normaliseWith f .: List.(++)
  mapKeysWith f v = normaliseWith v . map (mapFst f)
  mapVals f = map (mapSnd f)
  lookup = List.lookup


