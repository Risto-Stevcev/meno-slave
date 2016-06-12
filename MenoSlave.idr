module MenoSlave

%default total

-- This proof is based on the dialog between Socrates and one of Meno's slaves
-- Source: Plato, Meno, 84c

{- Diagammatic view of the square
  
  J-H-G
  |/ \|
  D C E
  |\ /|
  A-B-F
  
-}


{- Axioms

A square is a regular quadrilateral with four equal sides and angles with properties
The angles of a square add up to 360 degrees

A triangle is a polygon with three edges and vertices
The angles of a triangle add up to 180 degrees
An isosceles triangle is a triangle with two sides (and therefore two angles) of equal length

-}

-- Construct a square

data Square   : Double -> Type where
     MkSquare : Double -> Square a

testSquareReflexivity : Square 4 = Square (2 + 2)
testSquareReflexivity = Refl

testSquareReflexivity' : Square 3 = Square (3 + 1) -> Void
testSquareReflexivity' Refl impossible


-- Square functions

length : Square a -> Double
length (MkSquare x) = x

testLength : length (MkSquare 4) = 4.0
testLength = Refl


circumference : Square a -> Double
circumference (MkSquare x) = x * 4

testCircumference : circumference (MkSquare 4) = 16.0
testCircumference = Refl


area : Square a -> Double
area (MkSquare x) = x * x

testArea : area (MkSquare 5) = 25.0
testArea = Refl


-- Construct a square from four smaller squares

makeSquare : Square a -> Square b -> Square c -> Square d -> Square e
makeSquare w x y z = MkSquare (area w + area x + area y + area z)

testMakeSquare : makeSquare (MkSquare 1) (MkSquare 2) (MkSquare 3) (MkSquare 4) = (MkSquare 30)
testMakeSquare = Refl


-- Construct four equal squares

-- SOCRATES: Tell me, boy, is not this our square of four feet? (ABCD.) You understand?
-- BOY: Yes.
abcd : Square 4
abcd = MkSquare 4

-- SOCRATES: Now we can add another equal to it like this? (BCEF.)
-- BOY: Yes.
bcef : Square 4
bcef = MkSquare 4

-- SOCRATES: And a third here, equal to each of the others? (CEGH.)
-- BOY: Yes.
cegh : Square 4
cegh = MkSquare 4

-- SOCRATES: And then we can fill in this one in the comer? (DCHJ.)
-- BOY: Yes.
dchj : Square 4
dchj = MkSquare 4

-- SOCRATES: Then here we have four equal squares?
-- BOY: Yes.
fourEqualSquares : MenoSlave.abcd = MenoSlave.bcef -> MenoSlave.bcef = MenoSlave.cegh -> MenoSlave.cegh = MenoSlave.dchj
fourEqualSquares Refl Refl = Refl

afgj : Square a 
afgj = makeSquare abcd bcef cegh dchj

-- 4 * 4 = 16, and 16 * 4 = 64
testSizeAFGJ : MenoSlave.afgj = (MkSquare 64)
testSizeAFGJ = Refl


-- Diagonal bisection of a square
-- To bisect a square diagonally in equal parts, we need to split one of it's angles into two equal pieces:
bisect90deg : 90.0 / 2 = 45
bisect90deg = Refl

-- This will split the square into two triangles
-- Since we know two of the angles, we can infer the length of the third angle:
partial triangleAngles : 90 + 45 + c = 180
triangleAngles {c = 45} = Refl

-- Since the unknown angle is equal to the split angle, we know that it has formed an isosceles triangle where the
-- non-diagonal sides are equal, which means that a diagonal split along a square creates two equal pieces


-- Construct a triangle
data Triangle   : Double -> Double -> Type where
     MkTriangle : Double -> Double -> Triangle a b

areaTriangle : Triangle a b -> Double
areaTriangle (MkTriangle x y) = x * y / 2


-- SOCRATES: Now does this line going from corner to corner cut each of these squares in half? (BEHD.)
-- BOY: Yes.

-- Cuts ABCD across DB, BCEF across BE, CEGH across EH, DCHJ across HD 

lenABCD : Double
lenABCD = length abcd

acbdHalved : areaTriangle (MkTriangle MenoSlave.lenABCD MenoSlave.lenABCD) + 
             areaTriangle (MkTriangle MenoSlave.lenABCD MenoSlave.lenABCD) = area MenoSlave.abcd
acbdHalved = Refl

-- Same type of proof holds for all other squares due being cut along their diagonals and having the same size 


-- SOCRATES: And how many such halves are there in this figure? (BEHD.)
-- BOY: Four.
-- SOCRATES: And how many in this one? (ABCD.)
-- BOY: Two.
-- SOCRATES: And what is the relation of four to two?
-- BOY: Double.
-- SOCRATES: How big is this figure then?
-- BOY: Eight feet.
-- SOCRATES: On what base?
-- BOY: This one.
-- SOCRATES: The line which goes from corner to corner of the square of four feet?
-- BOY: Yes.
-- SOCRATES: The technical name for it is 'diagonal'; so if we use that name, it is your personal opinion that the 
--           square on the diagonal of the original square is double its area.
-- BOY: That is so, Socrates.
