Borrowed' : Nat
Borrowed' = Z

Free' : Nat
Free' = S Z

data ResourceCmd : Type -> Nat -> Nat -> Type where
  Borrow : x -> ResourceCmd x (S Z) Z
  Release : x -> ResourceCmd x Z (S Z)

  Pure : ty -> ResourceCmd ty state state
  (>>=) : ResourceCmd a state1 state2 ->
          (a -> ResourceCmd a state2 state3) ->
          ResourceCmd a state1 state3

resourceProg : ResourceCmd Nat Free' Borrowed'
resourceProg = do (Borrow 0)
                  (Release 2)
                  (Borrow 1)
