import Shape

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture

%name Shape shape, shape1, shape2
%name Picture pic, pic1, pic2

pic1 : Picture
pic1 = Primitive (Triangle 0.0 0.0)

pic2 : Picture
pic2 = Primitive (Triangle 0.0 0.0)

pic3 : Picture
pic3 = Primitive (Triangle 0.0 0.0)

testPicture : Picture
testPicture = Combine pic1 (Combine pic2 pic3)

pictureArea : Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine pic pic1) = pictureArea pic + pictureArea pic1
pictureArea (Rotate x pic) = pictureArea pic
pictureArea (Translate x y pic) = pictureArea pic

triangleArea: Shape -> Maybe Double
triangleArea shape@(Triangle x y) = Just (area shape)
triangleArea _ = Nothing

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = Just (max x y)

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive shape) = triangleArea shape
biggestTriangle (Combine pic pic1) = maxMaybe (biggestTriangle pic)  (biggestTriangle pic1)
biggestTriangle (Rotate x pic) = biggestTriangle pic
biggestTriangle (Translate x y pic) = biggestTriangle pic

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3))
  (Primitive (Triangle 2 4))
testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3))
  (Primitive (Circle 4))
