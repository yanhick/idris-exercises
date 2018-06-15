import Data.Vect

total my_length : List a -> Nat
my_length [] = 0
my_length (x :: xs) = my_length xs + 1

total my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) = my_reverse xs ++ [x]

total my_map_list : (a -> b) -> List a -> List b
my_map_list f [] = []
my_map_list f (x :: xs) = f x :: my_map_list f xs

total my_map_vector : (a -> b) -> Vect n a -> Vect n b
my_map_vector f [] = []
my_map_vector f (x :: xs) = f x :: my_map_vector f xs
