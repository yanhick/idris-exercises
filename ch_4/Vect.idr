data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : (x : a) -> (xs : Vect k a) -> Vect (S k) a

append : Vect n elem -> Vect m elem -> Vect (n + m) elem
append [] y = y
append (x :: xs) y = x :: append xs y

zip : Vect n a -> Vect n b -> Vect n (a, b)
zip [] y = []
zip (x :: xs) (y :: z) = (x, y) :: zip xs z

vectTake : Fin n -> Vect n a -> Vect m a
