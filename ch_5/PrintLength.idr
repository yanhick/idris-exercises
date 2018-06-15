
printLonger : IO ()
printLonger = do
  x <- getLine
  y <- getLine
  putStrLn (show $ max (length x) (length y))

printLongerBind : IO ()
printLongerBind = getLine >>= \x => getLine >>= \y => putStrLn (show $ max (length x) (length y))

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
    then pure (Just (cast input))
    else pure Nothing

readPair : IO (String, String)
readPair = do str1 <- getLine
              str2 <- getLine
              pure (str1, str2)

usePair : IO ()
usePair = do (str1, str2) <- readPair
             putStrLn "hello"


readNumbers : IO (Maybe (Nat, Nat))
readNumbers =
  do Just num1_ok <- readNumber | Nothing => pure Nothing
     Just num2_ok <- readNumber | Nothing => pure Nothing
     pure (Just (num1_ok, num2_ok))
