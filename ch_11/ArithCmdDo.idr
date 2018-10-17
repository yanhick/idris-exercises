import Data.Primitives.Views
import System
%default total

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  ReadFile : String -> Command (Either FileError String)
  WriteFile: String -> String -> Command (Either FileError ())
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (ReadFile x) = readFile x
runCommand (WriteFile x y) = writeFile x y
runCommand (Pure x) = pure x
runCommand (Bind x f) = do res <- runCommand x
                           runCommand (f res)

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
(>>=) = Do

data Input = Answer Int
           | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                        then Pure QuitCmd
                        else Pure (Answer (cast answer))

mutual
  correct : Stream Int -> (score : Nat) -> (attempts : Nat) -> ConsoleIO (Nat, Nat)
  correct nums score attempts
          = do PutStr "Correct!\n"
               quiz nums (score + 1) (attempts + 1)

  wrong : Stream Int -> Int -> (score : Nat) -> (attempts : Nat) -> ConsoleIO (Nat, Nat)
  wrong nums ans score attempts
        = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
             quiz nums score (attempts + 1)

  quiz : Stream Int -> (score : Nat) -> (attempts : Nat) -> ConsoleIO (Nat, Nat)
  quiz (num1 :: num2 :: nums) score attempts
    = do PutStr ("Score so far: " ++ show score ++ " / " ++ show attempts ++ "\n")
         input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
         case input of
              Answer answer => if answer == num1 * num2
                                  then correct nums score attempts
                                  else wrong nums (num1 * num2) score attempts
              QuitCmd => Quit (score, attempts)

data Fuel = Dry | More (Lazy Fuel)

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                  (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run x (Quit val) = do pure (Just val)
run (More fuel) (Do c f) = do res <- runCommand c
                              run fuel (f res)
run Dry p = pure Nothing

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = do seed <- time
          Just (score, attempts) <- run forever (quiz (arithInputs (fromInteger seed)) 0 0)
              | Nothing => putStrLn "Ran out of fuel"
          putStrLn ("Final score: " ++ show score ++ " / " ++ show attempts)

data ShellCommand = Cat String | Copy String String | Exit

parseShell : String -> Maybe ShellCommand
parseShell s = case split (== ' ') s of
  ["exit"] => Just Exit
  ["cat", path] => Just $ Cat path
  ["copy", src, dest] => Just $ Copy src dest
  _ => Nothing

readShellInput : Command ShellCommand
readShellInput = do input <- GetLine
                    case parseShell input of
                      Just shellCommand => Pure shellCommand
                      Nothing => Pure Exit

shell : ConsoleIO ()
shell = do
  input <- readShellInput
  case input of
    Cat filename => do (Right f) <- ReadFile filename
                          | Left _ => do PutStr "couldn't read file"
                                         Quit ()
                       PutStr f
                       shell
    Copy src dest => do (Right res) <- ReadFile src
                            | Left _ => do PutStr "couldn't read file"
                                           Quit ()
                        WriteFile dest res
                        shell
    Exit => Quit ()

partial
mainShell : IO ()
mainShell = do
          Just () <- run forever shell
              | Nothing => putStrLn "Ran out of fuel"
          putStrLn ("Exit shell")
