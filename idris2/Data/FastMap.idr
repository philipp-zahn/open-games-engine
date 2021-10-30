module Data.FastMap

import Data.IOArray
import Data.Hash

export
record FastMap (key, val : Type) where
  constructor MkFastMap
  populated : Int -- how many entires are in use
  array : IOArray (key, val) -- the entires

-- private utilites to manipulate FastMaps

private
emptyFastMap : (size : Int) -> FastMap key val
emptyFastMap size = MkFastMap 0 (unsafePerformIO (newArray size))

private
getSize : FastMap key val -> Int
getSize = max . array

private
shouldReallocate : FastMap key val -> Bool
shouldReallocate map = populated map * 2 > getSize map

private 
hashKey : Hash key => (size : Int) -> key -> Int
hashKey size = (`mod` size) . hash

private
traverseArray : (a -> IO b) -> IOArray a -> IO b -> IO b
traverseArray f x initial = traverseRec 0 initial
  where
    traverseRec : Int -> IO b -> IO b
    traverseRec idx st = do let True = idx <= max x
                              | False => st
                            Just (v) <- readArray x idx
                              | _ => traverseRec (idx + 1) st
                            traverseRec (idx + 1) (f v)

-- realloc doubles the size of the array and reshuffles all keys
private
reallocUnsafe : Hash key => FastMap key val -> FastMap key val
reallocUnsafe (MkFastMap c a) = MkFastMap c (unsafePerformIO recomputeAllKeys)
  where
    recomputeAllKeys : IO (IOArray (key, val ))
    recomputeAllKeys = do 
      let newSize = (max a * 2)
      arr <- the (IO $ IOArray (key, val)) (newArray newSize)
      _ <- traverseArray (\(k, v) => writeArray arr (hashKey newSize k) (k, v)) arr (pure True)
      pure arr

private
reallocOrId : Hash key => FastMap key val -> FastMap key val
reallocOrId m = if shouldReallocate m then reallocUnsafe m else m

-- Public interface for fastmaps

export
lookup : Hash key => FastMap key val -> key -> Maybe val
lookup m k = snd <$> unsafePerformIO (readArray m.array (hashKey (getSize m) k))

export
empty : FastMap key val
empty = emptyFastMap 0

-- default hashmap has size 1024
export
singleton : Hash key => key -> val -> FastMap key val
singleton k v = MkFastMap 1 (unsafePerformIO updateArray)
  where
    updateArray : IO (IOArray (key, val))
    updateArray = do arr <- newArray 1024
                     let hashedKey = hashKey 1024 k
                     _ <- writeArray arr hashedKey (k, v)
                     pure arr

export
addOneWithOnto : Hash key => (val -> val -> val) -> key -> val -> FastMap key val -> IO () 
addOneWithOnto f k v m =
  let m' = reallocOrId m 
      foundValue = lookup m' k
      addValue : val -> IO () = \v => ignore $ writeArray m'.array (hashKey (getSize m') k) (k, v)
  in case foundValue of
          -- The result of the lookup could also return the key stored with the value and check for collisions
          -- we could crash in case of collision or just log it for testing
          Just (value) => addValue (f value v)
          Nothing => addValue v

export
addOne : Hash key => Monoid val => key -> val -> FastMap key val -> FastMap key val
-- addOne = addOneWithOntoUnsafe (<+>)

-- -- should merge allocate a new one?
-- export
-- mergeOntoUnsafe : (m, onto: FastMap key val) -> FastMap key val
-- 
-- export
-- merge : FastMap key val -> FastMap key val -> FastMap key val
-- 
-- export
-- mapValues : (val -> val') -> FastMap key val -> FastMap key val'
-- 
export
mapKeysWithOnto : Hash key' => (key -> key') -> (val -> val -> val) 
                     -> FastMap key val -> FastMap key' val -> IO () 
mapKeysWithOnto f comb m onto = 
  traverseArray (\(k, v) => addOneWithOnto comb (f k) v onto) m.array (pure ())

export
mapKeysWithOntoUnsafe : Hash key' => (key -> key') -> (val -> val -> val) 
                     -> FastMap key val -> FastMap key' val -> FastMap key' val
mapKeysWithOntoUnsafe f comb m onto = 
  unsafePerformIO (mapKeysWithOnto f comb m onto *> pure onto)

export
mapKeysWith : Hash key' => (key -> key') -> (val -> val -> val) -> FastMap key val -> FastMap key' val
mapKeysWith f comb m = mapKeysWithOntoUnsafe f comb m (emptyFastMap (getSize m))

export
mapKeys : Hash key' => Monoid val => (key -> key') -> FastMap key val -> FastMap key' val
mapKeys f = mapKeysWith f (<+>)

{-
-}
