data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Functor Tree where
  map func Empty = Empty
  map func (Node left e right)
      = Node (map func left)
             (func e)
             (map func right)

totalLen : List String -> Nat
totalLen xs = foldr (\str, len => length str + len) 0 xs

Foldable Tree where
  foldr func acc Empty = acc
  foldr func acc (Node left e right)
        = let leftfold = foldr func acc left
              rightfold = foldr func leftfold right  in
              func e rightfold


data Vect : (len : Nat) -> (elem : Type) -> Type where
  Nil  : Vect Z elem
  (::) : (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem

(Eq elem, Ord elem) => Eq (Vect len elem) where
  (==) Nil Nil = True
  (==) ((::) x xs) ((::) y ys) = case compare x y of
                       EQ => xs == ys
                       _ => False

Foldable (Vect n) where
  foldr func acc Nil = acc
  foldr func acc (x :: xs) = let elemAcc = func x acc in foldr func elemAcc xs
