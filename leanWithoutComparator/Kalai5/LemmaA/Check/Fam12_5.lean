import Kalai5.LemmaA.Data.Fam12

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam12_t50_ok : fam12.walk [(5,1),(8,-1),(4,-1),(0,-1),(1,1),(2,1)] fam12_t50 = true := by decide +kernel

theorem fam12_t51_ok : fam12.walk [(8,0),(4,-1),(0,-1),(1,1),(2,1)] fam12_t51 = true := by decide +kernel

theorem fam12_t52_ok : fam12.walk [(8,1),(4,-1),(0,-1),(1,1),(2,1)] fam12_t52 = true := by decide +kernel

theorem fam12_t53_ok : fam12.walk [(4,0),(0,-1),(1,1),(2,1)] fam12_t53 = true := by decide +kernel

theorem fam12_t54_ok : fam12.walk [(4,1),(0,-1),(1,1),(2,1)] fam12_t54 = true := by decide +kernel

theorem fam12_t55_ok : fam12.walk [(0,0),(1,1),(2,1)] fam12_t55 = true := by decide +kernel

theorem fam12_t56_ok : fam12.walk [(6,-1),(0,1),(1,1),(2,1)] fam12_t56 = true := by decide +kernel

theorem fam12_t57_ok : fam12.walk [(6,0),(0,1),(1,1),(2,1)] fam12_t57 = true := by decide +kernel

theorem fam12_t58_ok : fam12.walk [(8,-1),(6,1),(0,1),(1,1),(2,1)] fam12_t58 = true := by decide +kernel

theorem fam12_t59_ok : fam12.walk [(8,0),(6,1),(0,1),(1,1),(2,1)] fam12_t59 = true := by decide +kernel

theorem fam12_t60_ok : fam12.walk [(5,-1),(8,1),(6,1),(0,1),(1,1),(2,1)] fam12_t60 = true := by decide +kernel

theorem fam12_t61_ok : fam12.walk [(5,0),(8,1),(6,1),(0,1),(1,1),(2,1)] fam12_t61 = true := by decide +kernel

end Kalai5.LemmaA
