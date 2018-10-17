
data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()

  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

(>>=) : State stateType a -> (a -> State stateType b) -> State stateType b
(>>=) = Bind

data Tree a = Empty
            | Node (Tree a) a (Tree a)

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = Pure Empty
treeLabelWith (Node left val right)
  = do left_labelled <- treeLabelWith left
       (this :: rest) <- Get
       Put rest
       right_labelled <- treeLabelWith left
       Pure (Node left_labelled (this, val) right_labelled)

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put x) st = ((), st)
runState (Pure x) st = (x, st)
runState (Bind x f) st = let (val, nextState) = runState x st in
                             runState (f val) nextState

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = fst (runState (treeLabelWith tree) [1..])
