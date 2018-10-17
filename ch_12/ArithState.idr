import Data.Primitives.Views
import System
%default total



record Score where
       constructor MkScore
       correct : Nat
       attempted: Nat

record GameState where
       constructor MkGameState
       score : Score
       difficulty : Int

initState : GameState
initState = MkGameState (MkScore 0 0) 12

Show GameState where
  show st = show (correct (score st)) ++ "/" ++
            show (attempted (score st))  ++ "\n" ++
            "Difficulty: "  ++ show (difficulty st)

setDifficulty : Int -> GameState -> GameState
setDifficulty newDiff = record { difficulty = newDiff }

addWrong : GameState -> GameState
addWrong state
  = record { score->attempted $= (+1) } state

addCorrect : GameState -> GameState
addCorrect state
  = record { score->correct $= (+1),
             score->attempted $= (+1) } state

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

mutual
  Functor Command where
    map func x = do val <- x
                    pure (func val)

  Applicative Command where
    pure = Pure
    (<*>) f a = do f' <- f
                   a' <- a
                   pure (f' a')

  Monad Command where
    (>>=) = Bind

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
(>>=) = Do

data Input = Answer Int
           | QuitCmd

mutual
  correct : ConsoleIO GameState
  correct = do PutStr "Correct!\n"
               st <- GetGameState
               PutGameState (addCorrect st)
               quiz

  wrong : Int -> ConsoleIO GameState
  wrong ans = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
                 st <- GetGameState
                 PutGameState (addWrong st)
                 quiz

  readInput : (prompt : String) -> Command Input

  quiz : ConsoleIO GameState
  quiz = do num1 <- GetRandom
            num2 <- GetRandom
            st <- GetGameState
            PutStr (show st ++ "\n")

            input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
            case input of
                 Answer answer => if answer == num1 * num2
                                     then correct
                                     else wrong (num1 * num2)
                 QuitCmd => Quit st

runCommand : Stream Int -> GameState -> Command a -> IO (a, Stream Int, GameState)
runCommand xs x (PutStr y) = do putStr y
                                pure ((), xs, x)
runCommand xs x GetLine = do str <- getLine
                             pure (str, xs, x)
runCommand (value :: xs) x GetRandom
  = pure (getRandom value (difficulty x), xs, x)
  where
    getRandom : Int -> Int -> Int
    getRandom val max with (divides val max)
      getRandom val 0 | DivByZero = 1
      getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1

runCommand xs x GetGameState = pure (x, xs, x)
runCommand xs x (PutGameState y) = pure ((), xs, y)
runCommand xs x (Pure y) = pure (y, xs, x)
runCommand xs x (Bind y f) = do (res, newRnds, newState) <- runCommand xs x y
                                runCommand newRnds newState (f res)

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> Stream Int -> GameState -> ConsoleIO a ->
      IO (Maybe a, Stream Int, GameState)
run fuel rnds state (Quit val) = do pure (Just val, rnds, state)
run (More fuel) rnds state (Do c f)
  = do (res, newRnds, newState) <- runCommand rnds state c
       run fuel newRnds newState (f res)
run Dry rnds state p = pure (Nothing, rnds, state)

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = do seed <- time
          (Just score, _, state) <-
            run forever (randoms (fromInteger seed)) initState quiz
                | _ => putStrLn "Ran out of fuel"
          putStrLn ("Final score: " ++ show state)

updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = Bind GetGameState (\s => PutGameState (f s))

record Votes where
       constructor MkVotes
       upvotes : Integer
       downvotes : Integer

record Article where
       constructor MkArticle
       title : String
       url : String
       score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

getScore : Article -> Integer
getScore (MkArticle title url (MkVotes upvotes downvotes)) = upvotes - downvotes

badSite : Article
badSite = MkArticle "Bad Page" "http://example.com/bad" (MkVotes 5 47)

goodSite : Article
goodSite = MkArticle "Good Page" "http://example.com/good" (MkVotes 101 7)

addUpvote : Article -> Article
addUpvote state = record { score->upvotes $= (+1) } state

addDownvote : Article -> Article
addDownvote state = record { score->downvotes $= (+1) } state
