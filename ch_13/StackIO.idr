import Data.Vect
%default total

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)

  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height

  Pure : ty -> StackCmd ty height height
  (>>=) : StackCmd a height1 height2 ->
          (a -> StackCmd b height2 height3) ->
          StackCmd b height1 height3


runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           IO (ty, Vect outHeight Integer)
runStack stk (Push val) = pure ((), val :: stk)
runStack (val :: stk) Pop = pure (val, stk)
runStack (val :: stk) Top = pure (val, val :: stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk GetStr = do x <- getLine
                         pure (x, stk)
runStack stk (PutStr x) = do putStr x
                             pure ((), stk)
runStack stk (x >>= f) = do (x', newStk) <- runStack stk x
                            runStack newStk (f x')

data StackIO : Nat -> Type where
  Do : StackCmd a height1 height2 ->
       (a -> Inf (StackIO height2)) -> StackIO height1

namespace StackDo
  (>>=) : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) -> StackIO height1
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry xs y = pure ()
run (More fuel) stk (Do c f) = do (res, newStk) <- runStack stk c
                                  run fuel newStk (f res)

data StkInput = Number Integer
              | Add
              | Multiply
              | Substract
              | Negate
              | Discard
              | Duplicate

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "substract" = Just Substract
strToInput "multiply" = Just Multiply
strToInput "negate" = Just Negate
strToInput "discard" = Just Discard
strToInput "duplicate" = Just Duplicate
strToInput x = if all isDigit (unpack x)
                  then Just (Number (cast x))
                  else Nothing

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push (val1 + val2)

doMultiply : StackCmd () (S (S height)) (S height)
doMultiply = do val1 <- Pop
                val2 <- Pop
                Push (val1 * val2)

doSubstract : StackCmd () (S (S height)) (S height)
doSubstract = do val1 <- Pop
                 val2 <- Pop
                 Push (val2 - val1)

doNegate : StackCmd () (S height) (S height)
doNegate = do val <- Pop
              Push (val * -1)

mutual
  tryAdd : StackIO height
  tryAdd { height = (S (S h)) }
    = do doAdd
         result <- Top
         PutStr (show result ++ "\n")
         stackCalc
  tryAdd
    = do PutStr "Fewer than two items on the stack\n"
         stackCalc

  trySubstract : StackIO height
  trySubstract { height = (S (S h)) }
    = do doSubstract
         result <- Top
         PutStr (show result ++ "\n")
         stackCalc
  trySubstract
    = do PutStr "Fewer than two items on the stack\n"
         stackCalc

  tryMultiply : StackIO height
  tryMultiply { height = (S (S h)) }
    = do doMultiply
         result <- Top
         PutStr (show result ++ "\n")
         stackCalc
  tryMultiply
    = do PutStr "Fewer than two items on the stack\n"
         stackCalc

  tryNegate : StackIO height
  tryNegate { height = (S h) }
    = do doNegate
         result <- Top
         PutStr (show result ++ "\n")
         stackCalc
  tryNegate
    = do PutStr "Empty stack\n"
         stackCalc

  tryDiscard : StackIO height
  tryDiscard { height = (S h) }
    = do result <- Pop
         PutStr (show result ++ "\n")
         stackCalc
  tryDiscard
    = do PutStr "Empty stack\n"
         stackCalc

  tryDuplicate : StackIO height
  tryDuplicate { height = (S h) }
    = do result <- Pop
         Push result
         Push result
         PutStr (show result ++ "\n")
         stackCalc
  tryDuplicate
    = do PutStr "Empty stack\n"
         stackCalc

  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                      Nothing => do PutStr "Invalid input\n"
                                    stackCalc
                      Just (Number x) => do Push x
                                            stackCalc
                      Just Add => tryAdd
                      Just Substract => trySubstract
                      Just Multiply => tryMultiply
                      Just Negate => tryNegate
                      Just Discard => tryDiscard
                      Just Duplicate => tryDuplicate

partial
main : IO ()
main = run forever [] stackCalc
