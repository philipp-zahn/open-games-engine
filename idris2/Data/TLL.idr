||| Type Level Lists
module Data.TLL

public export
data TypeList : List Type -> Type where
  Nil : TypeList []
  (::) : (_ : ty) -> TypeList ts -> TypeList (ty :: ts)


public export
Tuplelize : List Type -> Type
Tuplelize [] = ()
Tuplelize [x] = x
Tuplelize (x :: xs) = Pair x (Tuplelize xs)

public export
(++) : TypeList xs -> TypeList ys -> TypeList (xs ++ ys)
(++) [] y = y
(++) (ty :: x) y = ty :: (x ++ y)

public export
split : {xs : _} -> TypeList (xs ++ ys) -> (TypeList xs, TypeList ys)
split x {xs = []} = ([], x)
split (x :: z) {xs = (y :: xs)} = let (p1, p2) = split z in (x :: p1, p2)

public export
left : {xs : _} -> TypeList (xs ++ ys) -> TypeList xs
left = fst . split

public export
right : {xs : _} -> TypeList (xs ++ ys) -> TypeList ys
right = snd . split

public export
choice : (select : Bool) -> (b : TypeList ks) -> (b' : TypeList ks')
      -> TypeList (if select then ks else ks')
choice True b b' = b
choice False b b' = b'

{-
-}
