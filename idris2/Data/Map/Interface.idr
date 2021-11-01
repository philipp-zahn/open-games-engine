module Data.Map.Interface

import Data.List
import Data.SortedMap
import FFI.Hashtable

public export
interface Map constraint (0 m : Type -> Type -> Type) where
  constructor IMap
  ||| The empty map
  empty : constraint k => m k v

  ||| A map with a single element
  singleton : constraint k => k -> v -> m k v

  ||| Delete a key from the map, id if the key isn't found
  delete : constraint k => k -> m k v -> m k v

  ||| merging two maps and using the provided function to deal with collisions
  mergeWith : constraint k => (v -> v -> v) -> m k v -> m k v -> m k v

  ||| Map keys with possible collisions
  mapKeysWith : constraint k' => (k -> k') -> (v -> v -> v) -> m k v -> m k' v

  ||| Map values of the map
  mapVals : (v -> v') -> m k v -> m k v'

  ||| Lookup a value in the map
  lookup : Eq k => k -> m k v -> Maybe v
  
  ||| List conversion
  fromList : constraint k => List (k, v) -> m k v
  toList : m k v -> List (k, v)

export
mapKeys : Map c m => c k' => Semigroup v => (k -> k') -> m k v -> m k' v
mapKeys f = mapKeysWith {constraint=c} f (<+>)

export
merge : Map c m => c k => Semigroup v => m k v -> m k v -> m k v
merge = mergeWith {constraint=c} (<+>)

public export
LookupList : (k, v : Type) -> Type
LookupList k v = List (k, v)

private
normaliseWith : Eq k => (v -> v -> v) -> LookupList k v -> LookupList k v
normaliseWith f xs = normaliseAcc xs []
  where
    normaliseAcc : LookupList k v -> LookupList k v -> LookupList k v
    normaliseAcc [] ys = ys
    normaliseAcc (y@(key, val) :: xs) ys = case List.lookup key ys of
                                                Nothing => normaliseAcc xs (y :: ys)
                                                Just val' => normaliseAcc xs ((key, f val val') :: ys)

namespace List

  export
  implementation Map Eq LookupList where
    empty = []
    singleton k v = pure (k, v)
    delete k = filter ((/= k) . fst)
    mergeWith f = normaliseWith f .: List.(++)
    mapKeysWith f v = normaliseWith v . map (mapFst f)
    mapVals f = map (mapSnd f)
    lookup = List.lookup
    fromList = id
    toList = id

namespace SortedMap
  export
  implementation Map Ord SortedMap where
    empty = empty
    singleton = SortedMap.singleton
    delete = SortedMap.delete 
    mergeWith = SortedMap.mergeWith
    mapKeysWith f v = SortedMap.fromList . normaliseWith v . map (mapFst f) . SortedMap.toList
    lookup = lookup
    mapVals = map
    fromList = SortedMap.fromList
    toList = SortedMap.toList

namespace Hashtable

  export
  implementation Map (const ()) HashMap where
    empty = empty
    singleton = Hashtable.singleton
    delete = Hashtable.delete 
    mergeWith = ?noMerge -- Hashtable.mergeWith
    mapKeysWith f v = ?noMapKeys -- fromList . normaliseWith v . map (mapFst f) . toList
    lookup = lookup
    mapVals = map
    fromList = Hashtable.fromList
    toList = Hashtable.toList

