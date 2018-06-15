module Main

import System

countdown : (secs : Nat) -> IO ()
countdown Z = putStrLn "Lift off!"
countdown (S secs) = do putStrLn (show (S secs))
                        usleep 1000000
                        countdown secs

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
    then pure (Just (cast input))
    else pure Nothing

countdowns : IO ()
countdowns = do putStr "Enter starting number: "
                Just startNum <- readNumber
                     | Nothing => do putStrLn "Ivalid input"
                                     countdowns
                countdown startNum
                putStr "Another (y/n)"
                yn <- getLine
                if yn == "y" then countdowns
                             else pure ()

guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = do putStrLn ("Enter guess " ++ show guesses)
                          Just numGuess <- readNumber
                          | Nothing => do putStrLn "Invalid input"
                                          guess target (S guesses)
                          case compare target numGuess of
                            LT => do putStrLn "target is smaller"
                                     guess target (S guesses)
                            GT => do putStrLn "target is bigger"
                                     guess target (S guesses)
                            EQ => do putStrLn "correct"
                                     pure ()

randomGuess : IO ()
randomGuess = do epoch <- time
                 guess (cast (mod epoch 100)) Z

repl' : (prompt : String) -> (onInput : String -> String) -> IO ()
repl' prompt onInput = do putStrLn prompt
                          input <- getLine
                          if input == "" then pure ()
                                         else do putStrLn $ onInput input
                                                 repl' prompt onInput

replWith' : Show a => (state : a) -> (prompt : String) -> (onInput : a -> String -> Maybe (String, a)) -> IO ()
replWith' state prompt onInput = do putStrLn prompt
                                    putStrLn (show state)
                                    input <- getLine
                                    if input == ""
                                      then pure ()
                                      else let res = onInput state input in
                                        case res of
                                          Just (output, newState) => do
                                            putStrLn output
                                            replWith' newState prompt onInput
                                          Nothing => pure ()
