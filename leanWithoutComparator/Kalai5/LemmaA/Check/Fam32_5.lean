import Kalai5.LemmaA.Data.Fam32

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam32_t50_ok : fam32.walk [(0,1),(3,-1),(2,1)] fam32_t50 = true := by decide +kernel

theorem fam32_t51_ok : fam32.walk [(9,-1),(3,0),(2,1)] fam32_t51 = true := by decide +kernel

theorem fam32_t52_ok : fam32.walk [(9,0),(3,0),(2,1)] fam32_t52 = true := by decide +kernel

theorem fam32_t53_ok : fam32.walk [(7,-1),(11,-1),(1,-1),(0,-1),(9,1),(3,0),(2,1)] fam32_t53 = true := by decide +kernel

theorem fam32_t54_ok : fam32.walk [(7,0),(11,-1),(1,-1),(0,-1),(9,1),(3,0),(2,1)] fam32_t54 = true := by decide +kernel

theorem fam32_t55_ok : fam32.walk [(7,1),(11,-1),(1,-1),(0,-1),(9,1),(3,0),(2,1)] fam32_t55 = true := by decide +kernel

theorem fam32_t56_ok : fam32.walk [(11,0),(1,-1),(0,-1),(9,1),(3,0),(2,1)] fam32_t56 = true := by decide +kernel

theorem fam32_t57_ok : fam32.walk [(11,1),(1,-1),(0,-1),(9,1),(3,0),(2,1)] fam32_t57 = true := by decide +kernel

theorem fam32_t58_ok : fam32.walk [(1,0),(0,-1),(9,1),(3,0),(2,1)] fam32_t58 = true := by decide +kernel

theorem fam32_t59_ok : fam32.walk [(1,1),(0,-1),(9,1),(3,0),(2,1)] fam32_t59 = true := by decide +kernel

theorem fam32_t60_ok : fam32.walk [(0,0),(9,1),(3,0),(2,1)] fam32_t60 = true := by decide +kernel

theorem fam32_t61_ok : fam32.walk [(0,1),(9,1),(3,0),(2,1)] fam32_t61 = true := by decide +kernel

end Kalai5.LemmaA
