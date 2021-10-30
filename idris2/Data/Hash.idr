module Data.Hash



public export
interface Hash a where
  hash : a -> Int
  k
-- private 

private
prime : Int
prime = 71

private
combine : Hash a => Hash b => a -> b -> Int
combine x y = prime * (prime + hash x) + hash y

-- public 
export
Hash Int where
  hash = id

export
implementation Hash a => Hash b => Hash (a, b) where
  hash = uncurry combine 

export
Traversable t => Hash a => Hash (t a ) where
  hash = foldl (\acc, v => prime * acc + hash v) 1

export
Hash Double where
  hash = cast
