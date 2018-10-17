data InfIO : Type where
  Do : IO a
       -> (a -> Inf InfIO)
       -> InfIO

loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg)
                   (\_ => loopPrint msg)

run : InfIO -> IO ()
run (Do action cont) = do res <- action
                          run (cont res)

data Fuel = Dry | More Fuel

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run2 : Fuel -> InfIO -> IO ()
run2 (More fuel) (Do c f) = do res <- c
                               run2 fuel (f res)
run2 Dry p = putStrLn "Out of fuel"

data Fuel' = Dry' | More' (Lazy Fuel')

forever : Fuel'
forever = More' forever

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

loopPrint' : String -> InfIO
loopPrint' msg = do putStrLn msg
                    loopPrint msg
