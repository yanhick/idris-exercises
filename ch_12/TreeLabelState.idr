import Control.Monad.State

data Tree a = Empty
            | Node (Tree a) a (Tree a)

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node left val right)
  = do left_labelled <- treeLabelWith left
       (this :: rest) <- get
       put rest
       right_labelled <- treeLabelWith left
       pure (Node left_labelled (this, val) right_labelled)

treeLabel :  Tree a -> Tree (Integer, a)
treeLabel tree = evalState (treeLabelWith tree) [1..]

update : (stateType -> stateType) -> State stateType ()
update f = do current <- get
              put (f current)

increase : Nat -> State Nat ()
increase k = update (+k)

treeCountEmpty : Tree a -> State Nat ()
treeCountEmpty Empty = do current <- get
                          put (S current)
treeCountEmpty (Node left val right)
  = do treeCountEmpty left
       treeCountEmpty right

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

countEmpty : Tree a -> State Nat ()
countEmpty = treeCountEmpty

countEmptyNode: Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = do (empty, node) <- get
                          put ((S empty, node))
countEmptyNode (Node left val right)
  = do (empty, node) <- get
       put (empty, S node)
       countEmptyNode left
       countEmptyNode right
