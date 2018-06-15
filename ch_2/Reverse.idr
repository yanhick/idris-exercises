module Main

palindrome : Nat -> String -> Bool
palindrome l str = (length str > l) && (toLower str == toLower (reverse str))

counts : String -> (Nat, Nat)
counts str = (length (words str), length str)

top_ten : Ord a => List a -> List a
top_ten xs = take 10 (reverse (sort xs))

over_length : Nat -> List String -> Nat
over_length l xs = length (filter ((> l) . length) xs)


main : IO ()
main = do
  putStrLn "Enter a string (palindrome)"
  line <- getLine
  print (palindrome 1 line)
  putStrLn "Enter a string (counts)"
  line <- getLine
  print (counts line)
