module FFI.Hashtable

import Data.List

%default total

export
data HashMap : Type -> Type -> Type where [external]

%foreign "scheme:idris-make-hashtable"
prim__makeHashMap : HashMap k v

%foreign "scheme:idris-hashtable-set"
prim__hashtableSet : HashMap k v -> k -> v -> HashMap k v

%foreign "scheme:idris-hashtable-ref"
prim__hashtableRef : HashMap k v -> k -> Maybe v

%foreign "scheme:idris-hashtable-contains"
prim__hashtableContains : HashMap k v -> k -> Bool

%foreign "scheme:idris-hashtable-update"
prim__hashtableUpdate : HashMap k v -> k -> (v -> v) -> v -> HashMap k v

%foreign "scheme:idris-hashtable-delete"
prim__hashtableDelete : HashMap k v -> k -> HashMap k v

%foreign "scheme:idris-hashtable-size"
prim__hashtableSize : HashMap k v -> Nat

%foreign "scheme:idris-hashtable-keys"
prim__hashtableKeys : HashMap k v -> List k

%foreign "scheme:idris-hashtable-entries"
prim__hashtableEntries : HashMap k v -> (List k, List v)

export
empty : HashMap k v
empty = prim__makeHashMap

export
lookup : k -> HashMap k v -> Maybe v
lookup = flip prim__hashtableRef

export
contains : k -> HashMap k v -> Bool
contains = flip prim__hashtableContains

export
insert : k -> v -> HashMap k v -> HashMap k v
insert k v m = prim__hashtableSet m k v

export
insertWith : (v -> v -> v) -> k -> v -> HashMap k v -> HashMap k v
insertWith f key val m = 
  case lookup key m of
       Just val' => insert key (f val val') m
       Nothing => insert key val m

export
singleton : k -> v -> HashMap k v
singleton k v = insert k v empty

export
insertFrom : Foldable f => f (k, v) -> HashMap k v -> HashMap k v
insertFrom xs m = foldr (uncurry insert) m xs

export
delete : k -> HashMap k v -> HashMap k v
delete = flip prim__hashtableDelete

||| Applies the function to the value associated with the given key if present,
||| otherwise applies the function to the provided default value.
export
update : k -> (v -> v) -> v -> HashMap k v -> HashMap k v
update k f def m = prim__hashtableUpdate m k f def

export
fromList : List (k, v) -> HashMap k v
fromList = flip insertFrom empty

export
toList : HashMap k v -> List (k, v)
toList = uncurry zip . prim__hashtableEntries

export
mergeWith : (v -> v -> v) -> HashMap k v -> HashMap k v -> HashMap k v
mergeWith f m1 m2 = let m1' = Hashtable.toList m1 in foldr (uncurry (insertWith f)) m2 m1'

export
keys : HashMap k v -> List k
keys = prim__hashtableKeys

export
values : HashMap k v -> List v
values = snd . prim__hashtableEntries

export
size : HashMap k v -> Nat
size = prim__hashtableSize

export
Functor (HashMap k) where
  map f = fromList . map (\(k, v) => (k, f v)) . toList

export
Foldable (HashMap k) where
  foldr f acc = foldr (f . snd) acc . toList
  foldl f acc = foldl (flip (flip f . snd)) acc . Hashtable.toList
  null m = prim__hashtableSize m == 1
  foldMap f = foldMap (f . snd) . toList

export
Traversable (HashMap k) where
  traverse f = map fromList . traverse (\(k, v) => (k,) <$> f v) . Hashtable.toList

-- compile with option "--directive extraRuntime=path/to/support.ss"
