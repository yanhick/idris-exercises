import Data.Vect

append_nil : Vect m elem -> Vect (plus m 0) elem
append_nil {m} xs = rewrite plusZeroRightNeutral m in xs

append_xs : Vect (S (m + len)) elem -> Vect (plus m (S len)) elem
append_xs {m} {len} xs = rewrite sym (plusSuccRightSucc m len) in xs

append : Vect n elem -> Vect m elem -> Vect (m + n) elem
append [] ys = append_nil ys
append (x :: xs) ys = append_xs (x :: append xs ys)


myPlusCommutes : (n: Nat) -> (m: Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite plusZeroRightNeutral m in Refl
myPlusCommutes (S k) m = rewrite myPlusCommutes k m
                                 in rewrite plusSuccRightSucc m k
                                 in Refl

reverseProof_nil : Vect n a -> Vect (plus n 0) a
reverseProof_nil {n} acc = rewrite plusZeroRightNeutral n in acc

reverseProof_xs : Vect ((S n1) + len) a -> Vect (plus n1 (S len)) a
reverseProof_xs {n1} {len} xs = rewrite sym $ plusSuccRightSucc n1 len in xs

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n + m) a
        reverse' acc [] = reverseProof_nil acc
        reverse' acc (x :: ys) = reverseProof_xs (reverse' (x::acc) ys)
