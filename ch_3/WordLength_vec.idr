import Data.Vect

total allLengths : Vect len String -> Vect len Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words

allLengths2 : Vect len String -> Vect len Nat
allLengths2 [] = []
allLengths2 (x :: xs) = length x :: allLengths2 xs
