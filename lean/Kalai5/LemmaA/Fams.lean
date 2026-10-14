import Kalai5.LemmaA.Reduce
import Kalai5.LemmaA.Data.Fam0
import Kalai5.LemmaA.Data.Fam12
import Kalai5.LemmaA.Data.Fam15
import Kalai5.LemmaA.Data.Fam22
import Kalai5.LemmaA.Data.Fam26
import Kalai5.LemmaA.Data.Fam32
import Kalai5.LemmaA.Data.Fam38
import Kalai5.LemmaA.Data.Fam39
import Kalai5.LemmaA.Data.Fam44

/-! The nine certified Lemma A families (class representatives) with their shear data. -/

namespace Kalai5.LemmaA

def famX0 : FamX where
  F := fam0
  basis := [0,1,2,3]
  free := [4,5,6]
  N := [[-1,1,1,1],[-1,0,0,1],[-1,0,1,0],[-1,1,0,0]]
  D := 2

def famX12 : FamX where
  F := fam12
  basis := [0,1,2,4]
  free := [3,5,6]
  N := [[-1,1,1,1],[-1,0,0,1],[-1,0,1,0],[-1,1,0,0]]
  D := 2

def famX15 : FamX where
  F := fam15
  basis := [0,1,2,4]
  free := [3,5,6]
  N := [[-1,1,1,1],[-1,0,0,1],[-1,0,1,0],[-1,1,0,0]]
  D := 2

def famX22 : FamX where
  F := fam22
  basis := [0,1,2,3]
  free := [4,5,6]
  N := [[-1,1,1,1],[-1,0,0,1],[-1,0,1,0],[-1,1,0,0]]
  D := 2

def famX26 : FamX where
  F := fam26
  basis := [0,1,2,3]
  free := [4,5,6]
  N := [[-1,1,1,1],[-1,0,0,1],[-1,0,1,0],[-1,1,0,0]]
  D := 2

def famX32 : FamX where
  F := fam32
  basis := [0,1,2,4]
  free := [3,5,6]
  N := [[-1,1,1,1],[-1,0,0,1],[-1,0,1,0],[-1,1,0,0]]
  D := 2

def famX38 : FamX where
  F := fam38
  basis := [0,1,2,4]
  free := [3,5,6]
  N := [[-1,1,1,1],[-1,0,0,1],[-1,0,1,0],[-1,1,0,0]]
  D := 2

def famX39 : FamX where
  F := fam39
  basis := [0,1,2,4]
  free := [3,5,6]
  N := [[-1,1,1,1],[-1,0,0,1],[-1,0,1,0],[-1,1,0,0]]
  D := 2

def famX44 : FamX where
  F := fam44
  basis := [0,1,2,4]
  free := [3,5,6]
  N := [[-1,1,1,1],[-1,0,0,1],[-1,0,1,0],[-1,1,0,0]]
  D := 2

/-- In the order used by the table (`fam` indices). -/
def repFams : List FamX := [famX0, famX12, famX15, famX22, famX26, famX32, famX38, famX39, famX44]

end Kalai5.LemmaA
