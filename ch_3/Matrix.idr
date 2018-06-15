import Data.Vect

createEmpties : Vect n (Vect 0 elem)
createEmpties = replicate _ []

total transposeHelper : (x : Vect n elem) -> (xsTrans : Vect n (Vect len elem)) -> Vect n (Vect (S len) elem)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) = let xsTrans = transposeMat xs in
                            transposeHelper x xsTrans

transposeMat' : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat' [] = createEmpties
transposeMat' (x :: xs) = let xsTrans = transposeMat' xs in
                            zipWith (::) x xsTrans

total addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys


multTransposed : Num numType => (ysTrans : Vect p (Vect m numType)) -> (x : Vect m numType) -> Vect p numType
multTransposed [] x = []
multTransposed ys x = map (sum . zipWith (*) x) ys

multMatrix : Num numType => Vect n (Vect m numType) -> Vect m (Vect p numType) -> Vect n (Vect p numType)
multMatrix [] [] = []
multMatrix xs ys = let ysTrans = transposeMat ys in
                      map (multTransposed ysTrans) xs

decreasingVect : Vect n Nat
decreasingVect { n =  Z} = []
decreasingVect { n =  (S k)} = k :: decreasingVect
