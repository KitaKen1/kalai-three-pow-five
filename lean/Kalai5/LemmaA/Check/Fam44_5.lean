import Kalai5.LemmaA.Data.Fam44

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam44_t51_ok : fam44.walk [(0,1),(1,-1),(3,0)] fam44_t51 = true := by decide +kernel

theorem fam44_t52_ok : fam44.walk [(1,0),(3,0)] fam44_t52 = true := by decide +kernel

theorem fam44_t53_ok : fam44.walk [(0,-1),(1,1),(3,0)] fam44_t53 = true := by decide +kernel

theorem fam44_t54_ok : fam44.walk [(0,0),(1,1),(3,0)] fam44_t54 = true := by decide +kernel

theorem fam44_t55_ok : fam44.walk [(5,-1),(0,1),(1,1),(3,0)] fam44_t55 = true := by decide +kernel

theorem fam44_t56_ok : fam44.walk [(5,0),(0,1),(1,1),(3,0)] fam44_t56 = true := by decide +kernel

theorem fam44_t57_ok : fam44.walk [(5,1),(0,1),(1,1),(3,0)] fam44_t57 = true := by decide +kernel

theorem fam44_t58_ok : fam44.walk [(2,-1),(0,-1),(7,-1),(4,-1),(5,-1),(1,-1),(3,1)] fam44_t58 = true := by decide +kernel

theorem fam44_t59_ok : fam44.walk [(2,0),(0,-1),(7,-1),(4,-1),(5,-1),(1,-1),(3,1)] fam44_t59 = true := by decide +kernel

theorem fam44_t60_ok : fam44.walk [(2,1),(0,-1),(7,-1),(4,-1),(5,-1),(1,-1),(3,1)] fam44_t60 = true := by decide +kernel

theorem fam44_t61_ok : fam44.walk [(0,0),(7,-1),(4,-1),(5,-1),(1,-1),(3,1)] fam44_t61 = true := by decide +kernel

theorem fam44_t62_ok : fam44.walk [(0,1),(7,-1),(4,-1),(5,-1),(1,-1),(3,1)] fam44_t62 = true := by decide +kernel

end Kalai5.LemmaA
