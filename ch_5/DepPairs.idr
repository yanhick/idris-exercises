import Data.Vect

readVect : IO (len ** Vect len String)
readVect = do x <- getLine
              if (x == "")
                then pure (_ ** [])
                else do (_ ** xs) <- readVect
                        pure (_ ** x :: xs)

zipInputs : IO ()
zipInputs = do putStrLn "Enter first vector (blank line to end):"
               (len1 ** vec1) <- readVect
               putStrLn "Enter second vector (blank line to end):"
               (len2 ** vec2) <- readVect
               case exactLength len1 vec2 of
                 Nothing => putStrLn "Vectors are different lengths"
                 Just vec2' => printLn (zip vec1 vec2')

readToBlank : IO (List String)
readToBlank = do line <- getLine
                 if (line == "")
                   then pure []
                   else do lines <- readToBlank
                           pure (line :: lines)

readAndSave : IO ()
readAndSave = do putStrLn "Enter lines:"
                 lines <- readToBlank
                 putStrLn "Enter filename:"
                 filename <- getLine
                 Right _ <- writeFile filename (concat lines)
                 | Left err => do
                    putStrLn (show err)
                    pure ()
                 pure ()

readWithHandle : (file : File) -> IO (Either FileError (n ** Vect n String))
readWithHandle file = do
  isEOF <- fEOF file
  if isEOF
    then pure $ pure (_ ** [])
    else do
      Right line <- fGetLine file
      | Left err => do
          putStrLn (show err)
          pure $ pure (_ ** [])
      Right (len ** lines) <- readWithHandle file
      | Left err => do
          putStrLn (show err)
          pure $ pure (_ ** [])
      pure $ Right ((S len) ** (line :: lines))


readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right f <- openFile filename Read
  | Left err => do putStrLn (show err)
                   pure (_ ** [])
  Right lines <- readWithHandle f
  | Left err => do putStrLn (show err)
                   pure (_ ** [])
  pure lines
