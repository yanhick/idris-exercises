import Data.Vect


tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                      Nothing => Nothing
                      (Just x) => Just (index x xs)

vectTake : (f : Fin n) -> Vect n a -> Vect (finToNat f) a
vectTake FZ xs = []
vectTake (FS x) (y :: xs) = y :: vectTake x xs


sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys =
  case integerToFin pos n of
    Nothing => Nothing
    Just fin => Just $ index fin xs + index fin ys
