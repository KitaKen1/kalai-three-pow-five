import Kalai5.LemmaA.Data.Fam38

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam38_t52_ok : fam38.walk [(10,1),(0,-1),(8,-1),(11,-1),(3,-1),(2,1)] fam38_t52 = true := by decide +kernel

theorem fam38_t53_ok : fam38.walk [(0,0),(8,-1),(11,-1),(3,-1),(2,1)] fam38_t53 = true := by decide +kernel

theorem fam38_t54_ok : fam38.walk [(0,1),(8,-1),(11,-1),(3,-1),(2,1)] fam38_t54 = true := by decide +kernel

theorem fam38_t55_ok : fam38.walk [(8,0),(11,-1),(3,-1),(2,1)] fam38_t55 = true := by decide +kernel

theorem fam38_t56_ok : fam38.walk [(8,1),(11,-1),(3,-1),(2,1)] fam38_t56 = true := by decide +kernel

theorem fam38_t57_ok : fam38.walk [(11,0),(3,-1),(2,1)] fam38_t57 = true := by decide +kernel

theorem fam38_t58_ok : fam38.walk [(11,1),(3,-1),(2,1)] fam38_t58 = true := by decide +kernel

theorem fam38_t59_ok : fam38.walk [(8,-1),(10,-1),(1,-1),(0,-1),(11,-1),(3,0),(2,1)] fam38_t59 = true := by decide +kernel

theorem fam38_t60_ok : fam38.walk [(8,0),(10,-1),(1,-1),(0,-1),(11,-1),(3,0),(2,1)] fam38_t60 = true := by decide +kernel

theorem fam38_t61_ok : fam38.walk [(8,1),(10,-1),(1,-1),(0,-1),(11,-1),(3,0),(2,1)] fam38_t61 = true := by decide +kernel

theorem fam38_t62_ok : fam38.walk [(10,0),(1,-1),(0,-1),(11,-1),(3,0),(2,1)] fam38_t62 = true := by decide +kernel

theorem fam38_t63_ok : fam38.walk [(10,1),(1,-1),(0,-1),(11,-1),(3,0),(2,1)] fam38_t63 = true := by decide +kernel

end Kalai5.LemmaA
