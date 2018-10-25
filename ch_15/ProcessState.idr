import System.Concurrency.Channels

%default total

data ListAction : Type where
  Length : List elem -> ListAction
  Append : List elem -> List elem -> ListAction

ListType : ListAction -> Type
ListType (Length xs) = Nat
ListType (Append {elem} xs ys) = List elem

data ProcState = NoRequest | Sent | Complete

data MessagePID = MkMessage PID
data Message = Add Nat Nat

data Process : Type ->
               (in_state : ProcState) ->
               (out_state : ProcState) ->
               Type where
  Request : MessagePID -> Message -> Process Nat st st
  Respond : ((msg : Message) -> Process Nat NoRequest NoRequest) ->
            Process (Maybe Message) st Sent
  Spawn : Process () NoRequest Complete ->
          Process (Maybe MessagePID) st st
  Loop : Inf (Process a NoRequest Complete) ->
         Process a Sent Complete
  Action : IO a -> Process a st st
  Pure : a ->  Process a st st
  (>>=) : Process a st1 st2 -> (a -> Process b st2 st3) ->
          Process b st1 st3

Service : Type -> Type
Service a = Process a NoRequest Complete

Client : Type -> Type
Client a = Process a NoRequest NoRequest


procAdder : Service ()
procAdder = do Respond (\msg => case msg of
                                     Add x y => Pure (x + y))
               Loop procAdder

procMain : Client ()
procMain = do Just adder_id <- Spawn procAdder
                   | Nothing => Action (putStrLn "Spawn failed")
              answer <- Request adder_id (Add 2 3)
              Action (printLn answer)

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> Process t in_state out_state -> IO (Maybe t)
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
                     pure (Just x)
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
runProc : Process () in_state out_state -> IO ()
runProc proc = do run forever proc
                  pure ()
