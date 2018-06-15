
data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub

Abs ty => Abs (Expr ty) where
  abs = Abs


eval : (Neg num, Integral num, Abs num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs (eval x)

(Show ty, Abs ty) => Show (Expr ty) where
  show (Val x) = show x
  show (Add x y) = "(" ++ show x ++ "+" ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ "-" ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ "*" ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ "/" ++ show y ++ ")"
  show (Abs x) = show (abs x)

(Eq ty, Abs ty, Num ty, Neg ty, Integral ty, Ord ty) => Eq (Expr ty) where
  (==) expr expr' = case compare (eval expr) (eval expr') of
                         EQ => True
                         _ => False

(Abs ty, Integral ty, Neg ty) => Cast (Expr ty) ty where
  cast = eval

Functor Expr where
  map f (Val x) = Val (f x)
  map f (Add x y) = Add (map f x) (map f y)
  map f (Sub x y) = Sub (map f x) (map f y)
  map f (Mul x y) = Mul (map f x) (map f y)
  map f (Div x y) = Div (map f x) (map f y)
  map f (Abs x) = Abs (map f x)
