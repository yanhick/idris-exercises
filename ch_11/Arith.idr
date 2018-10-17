import Data.Primitives.Views

quiz : Stream Int -> (score : Nat) -> IO ()
quiz (num1 :: num2 :: nums) score
  = do putStrLn ("Score so far: " ++ show score)
       putStr (show num1 ++ " * " ++ show num2 ++ "? ")
       answer <- getLine
       if cast answer == num1 * num2
          then do putStrLn "Correct!"
                  quiz nums (score + 1)
          else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                  quiz nums score

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                  (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1


every_other : Stream Integer -> Stream Integer
every_other (num1 :: num2 :: xs) = num2 :: every_other xs

data Face = Heads | Tails

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z xs = []
coinFlips (S k) (value :: xs) = getFace value :: coinFlips k xs
  where
    bound : Int -> Int
    bound num with (divides num 2)
      bound ((2 * div) + rem) | (DivBy prf) = rem + 1

    getFace : Int -> Face
    getFace x = if bound x == 1 then Heads else Tails


square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx = let next = (approx + (number / approx)) / 2 in
                                        approx :: square_root_approx number next

square_root_bound :
  (max : Nat) -> (number : Double) -> (bound : Double) -> (approxs : Stream Double) -> Double
square_root_bound Z number bound (value :: xs) = value
square_root_bound (S k) number bound (value :: xs) = if ((value * value) - number < bound)
                                                        then value
                                                        else square_root_bound k number bound xs

square_root : (number : Double) -> Double
square_root number = square_root_bound 100 number 0.00000000001 (square_root_approx number number)
