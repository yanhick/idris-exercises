data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name InfList xs, yz, zs

MyInf : Type -> Type

MyDelay : (value : ty) -> Inf ty

Force : (computation : Inf ty) -> ty

countFrom : Integer -> InfList Integer
countFrom x = x :: countFrom (x + 1)

getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z xs = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

Functor InfList where
  map func ( x :: xs ) = func x :: map func xs
