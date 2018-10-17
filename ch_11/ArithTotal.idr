import Data.Primitives.Views
import System

%default total

data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> InfIO -> IO ()
run (More fuel) (Do c f) = do res <- c
                              run fuel (f res)
run Dry p = putStrLn "Out of fuel"

quiz : Stream Int -> (score : Nat) -> InfIO
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

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = do seed <- time
          run forever (quiz (arithInputs (fromInteger seed)) 0)

totalReplWith : (state : a)
                -> (prompt : String)
                -> (onInput : a -> String -> Maybe (String, a))
                -> InfIO

totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action = do
  putStr prompt
  line <- getLine
  putStr (action line)
  totalREPL prompt action
