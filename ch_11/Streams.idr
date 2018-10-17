labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith xs [] = []
labelWith (value :: xs) (x :: ys) = (value, x) :: labelWith xs ys

label : List a -> List (Integer, a)
label = labelWith (iterate (+1) 0)
