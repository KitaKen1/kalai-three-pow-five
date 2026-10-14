import Kalai5.LemmaA.Data.Fam38

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam38_t28_ok : fam38.walk [(0,0),(11,1),(3,0),(2,-1)] fam38_t28 = true := by decide +kernel

theorem fam38_t29_ok : fam38.walk [(1,-1),(0,1),(11,1),(3,0),(2,-1)] fam38_t29 = true := by decide +kernel

theorem fam38_t30_ok : fam38.walk [(1,0),(0,1),(11,1),(3,0),(2,-1)] fam38_t30 = true := by decide +kernel

theorem fam38_t31_ok : fam38.walk [(10,-1),(1,1),(0,1),(11,1),(3,0),(2,-1)] fam38_t31 = true := by decide +kernel

theorem fam38_t32_ok : fam38.walk [(10,0),(1,1),(0,1),(11,1),(3,0),(2,-1)] fam38_t32 = true := by decide +kernel

theorem fam38_t33_ok : fam38.walk [(8,-1),(10,1),(1,1),(0,1),(11,1),(3,0),(2,-1)] fam38_t33 = true := by decide +kernel

theorem fam38_t34_ok : fam38.walk [(8,0),(10,1),(1,1),(0,1),(11,1),(3,0),(2,-1)] fam38_t34 = true := by decide +kernel

theorem fam38_t35_ok : fam38.walk [(8,1),(10,1),(1,1),(0,1),(11,1),(3,0),(2,-1)] fam38_t35 = true := by decide +kernel

theorem fam38_t36_ok : fam38.walk [(11,-1),(3,1),(2,-1)] fam38_t36 = true := by decide +kernel

theorem fam38_t37_ok : fam38.walk [(11,0),(3,1),(2,-1)] fam38_t37 = true := by decide +kernel

theorem fam38_t38_ok : fam38.walk [(8,-1),(11,1),(3,1),(2,-1)] fam38_t38 = true := by decide +kernel

theorem fam38_t39_ok : fam38.walk [(8,0),(11,1),(3,1),(2,-1)] fam38_t39 = true := by decide +kernel

end Kalai5.LemmaA
