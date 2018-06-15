import Data.List.Views
import Data.Vect.Views
import Data.Nat.Views
import Data.Vect
%default total

mergeSort : Ord a => List a -> List a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec)
    = merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix input1 input2 with (snocList input1)
  equalSuffix [] input2 | Empty = []
  equalSuffix (xs ++ [x]) input2 | (Snoc xsrec) with (snocList input2)
    equalSuffix (xs ++ [x]) [] | (Snoc xsrec) | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec)
     = if x == y then (equalSuffix xs ys | xsrec | ysrec) ++ [x]
                 else []

mergeSortVec : Ord a => Vect n a -> Vect n a
mergeSortVec input with (splitRec input)
  mergeSortVec [] | SplitRecNil = []
  mergeSortVec [x] | SplitRecOne = [x]
  mergeSortVec (xs ++ ys) | (SplitRecPair lrec rrec)
    = merge (mergeSortVec xs | lrec) (mergeSortVec ys | rrec)

toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1"

main : IO ()
main = print (toBinary 94)

palindrome : Eq a => List a -> Bool
palindrome input with (vList input)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (xs ++ [y])) | (VCons rec)
    = if x == y then palindrome xs | rec
                else False
