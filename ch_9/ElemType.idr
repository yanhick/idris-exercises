data Vect : Nat -> Type -> Type where
  Nil : Vect 0 elem
  (::) : elem -> Vect len elem -> Vect (S len) elem

data Elem : a -> Vect k a -> Type where
  Here : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notHere : (x = value) -> Void) -> (notThere : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
isElem value [] = No notInNil
isElem value (x :: xs) = case decEq x value of
                             (Yes Refl) => Yes Here
                             (No notHere) => (case isElem value xs of
                                                  (Yes prf) => Yes (There prf)
                                                  (No notThere) => No (notInTail notHere notThere))


data ListElem : a -> List a -> Type where
  ListHere : ListElem x (x :: xs)
  ListThere : (later : ListElem x xs) -> ListElem x (y :: xs)

data Last : List a -> a -> Type where
     LastOne : Last [value] value
     LastCons : (prf : Last xs value) -> Last (x :: xs) value


lastNotInNil : Last [] value -> Void
lastNotInNil LastOne impossible
lastNotInNil (LastCons _) impossible

lastNotEqual : (contra : (x = value) -> Void) -> Last [x] value -> Void
lastNotEqual contra LastOne = contra Refl
lastNotEqual _ (LastCons LastOne) impossible
lastNotEqual _ (LastCons (LastCons _)) impossible

equalInTail : (prf : Last xs value) -> (contra : (xs = []) -> Void) -> Last (x :: xs) value
equalInTail LastOne contra = LastCons LastOne
equalInTail (LastCons prf) contra = LastCons (LastCons prf)

notEqualInTail : (contra1 : Last xs value -> Void) -> (contra : (xs = []) -> Void) -> Last (x :: xs) value -> Void
notEqualInTail contra1 contra LastOne = contra Refl
notEqualInTail contra1 contra (LastCons prf) = contra1 prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No lastNotInNil
isLast (x :: xs) value = case decEq xs [] of
                               (Yes Refl) => (case decEq x value of
                                                  (Yes Refl) => Yes LastOne
                                                  (No contra) => No (lastNotEqual contra))
                               (No contra) => (case isLast xs value of
                                                    (Yes prf) => Yes (equalInTail prf contra)
                                                    (No contra1) => No (notEqualInTail contra1 contra))
