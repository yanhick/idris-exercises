import Shape_abs

area : Shape -> Double
area s with (shapeView s)
  area (Triangle x y) | STriangle = 0.5 * x * y
  area (Rectangle x y) | SRectangle = x * y
  area (Circle x) | SCircle = pi * x * x
