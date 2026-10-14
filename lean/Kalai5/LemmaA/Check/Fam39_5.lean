import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_t52_ok : fam39.walk [(1,1),(0,-1),(14,1),(4,1),(3,1),(2,-1)] fam39_t52 = true := by decide +kernel

theorem fam39_t53_ok : fam39.walk [(0,0),(14,1),(4,1),(3,1),(2,-1)] fam39_t53 = true := by decide +kernel

theorem fam39_t54_ok : fam39.walk [(10,-1),(0,1),(14,1),(4,1),(3,1),(2,-1)] fam39_t54 = true := by decide +kernel

theorem fam39_t55_ok : fam39.walk [(10,0),(0,1),(14,1),(4,1),(3,1),(2,-1)] fam39_t55 = true := by decide +kernel

theorem fam39_t56_ok : fam39.walk [(5,-1),(10,1),(0,1),(14,1),(4,1),(3,1),(2,-1)] fam39_t56 = true := by decide +kernel

theorem fam39_t57_ok : fam39.walk [(5,0),(10,1),(0,1),(14,1),(4,1),(3,1),(2,-1)] fam39_t57 = true := by decide +kernel

theorem fam39_t58_ok : fam39.walk [(5,1),(10,1),(0,1),(14,1),(4,1),(3,1),(2,-1)] fam39_t58 = true := by decide +kernel

theorem fam39_t59_ok : fam39.walk [(2,0)] fam39_t59 = true := by decide +kernel

theorem fam39_t60_ok : fam39.walk [(5,-1),(10,-1),(0,-1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t60 = true := by decide +kernel

theorem fam39_t61_ok : fam39.walk [(5,0),(10,-1),(0,-1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t61 = true := by decide +kernel

theorem fam39_t62_ok : fam39.walk [(5,1),(10,-1),(0,-1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t62 = true := by decide +kernel

theorem fam39_t63_ok : fam39.walk [(10,0),(0,-1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t63 = true := by decide +kernel

end Kalai5.LemmaA
