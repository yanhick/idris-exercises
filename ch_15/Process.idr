import System.Concurrency.Channels

%default total

data MessagePID = MkMessage PID
data Message = Add Nat Nat

data Process : Type -> Type where
  Action : IO a -> Process a
  Pure : a -> Process a
  (>>=) : Process a -> (a -> Process b) -> Process b

  Loop : Inf (Process a) ->  Process a
  Spawn : Process () -> Process (Maybe MessagePID)
  Request : MessagePID -> Message -> Process (Maybe Nat)
  Respond : ((msg : Message) -> Process Nat) -> Process (Maybe Message)

procAdder : Process ()
procAdder = do Respond (\msg => case msg of
                                Add x y => Pure (x + y))
               Loop procAdder

procMain : Process ()
procMain = do Just adder_id <- Spawn procAdder
                   | Nothing => Action (putStrLn "Spawn failed")
              Just answer <- Request adder_id (Add 2 3)
                   | Nothing => Action (putStrLn "Request failed")
              Action (printLn answer)

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> Process t -> IO (Maybe t)
run Dry _ = pure Nothing
run fuel (Action x) = do res <- x
                         pure (Just res)
run fuel (Pure x) = pure (Just x)
run fuel (x >>= f) = do Just n <- run fuel x
                             | Nothing => pure Nothing
                        run fuel (f n)
run fuel (Spawn proc) = do Just pid <- spawn (do run fuel proc
                                                 pure ())
                                | Nothing => pure Nothing
                           pure (Just (Just (MkMessage pid)))
run fuel (Request (MkMessage process) msg)
  = do Just chan <- connect process
            | _ => pure Nothing
       ok <- unsafeSend chan msg
       if ok then do Just x <- unsafeRecv Nat chan
                          | Nothing => pure Nothing
                     pure (Just (Just x))
             else pure Nothing
run fuel (Respond calc)
  = do Just sender <- listen 1
            | Nothing => pure Nothing
       Just msg <- unsafeRecv Message sender
            | Nothing => pure Nothing
       res <- run fuel (calc msg)
       unsafeSend sender res
       pure (Just (Just msg))
run (More fuel) (Loop act) = run fuel act

partial
forever : Fuel
forever = More forever

partial
runProc : Process () -> IO ()
runProc proc = do run forever proc
                  pure ()
