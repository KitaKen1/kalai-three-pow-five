import Kalai5.LemmaA.Data.Fam22

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam22_t52_ok : fam22.walk [(14,1),(8,-1),(1,-1),(2,1)] fam22_t52 = true := by decide +kernel

theorem fam22_t53_ok : fam22.walk [(0,-1),(8,0),(1,-1),(2,1)] fam22_t53 = true := by decide +kernel

theorem fam22_t54_ok : fam22.walk [(0,0),(8,0),(1,-1),(2,1)] fam22_t54 = true := by decide +kernel

theorem fam22_t55_ok : fam22.walk [(6,-1),(0,1),(8,0),(1,-1),(2,1)] fam22_t55 = true := by decide +kernel

theorem fam22_t56_ok : fam22.walk [(6,0),(0,1),(8,0),(1,-1),(2,1)] fam22_t56 = true := by decide +kernel

theorem fam22_t57_ok : fam22.walk [(20,-1),(14,-1),(6,1),(0,1),(8,0),(1,-1),(2,1)] fam22_t57 = true := by decide +kernel

theorem fam22_t58_ok : fam22.walk [(20,0),(14,-1),(6,1),(0,1),(8,0),(1,-1),(2,1)] fam22_t58 = true := by decide +kernel

theorem fam22_t59_ok : fam22.walk [(4,-1),(20,1),(14,-1),(6,1),(0,1),(8,0),(1,-1),(2,1)] fam22_t59 = true := by decide +kernel

theorem fam22_t60_ok : fam22.walk [(4,0),(20,1),(14,-1),(6,1),(0,1),(8,0),(1,-1),(2,1)] fam22_t60 = true := by decide +kernel

theorem fam22_t61_ok : fam22.walk [(4,1),(20,1),(14,-1),(6,1),(0,1),(8,0),(1,-1),(2,1)] fam22_t61 = true := by decide +kernel

theorem fam22_t62_ok : fam22.walk [(14,0),(6,1),(0,1),(8,0),(1,-1),(2,1)] fam22_t62 = true := by decide +kernel

theorem fam22_t63_ok : fam22.walk [(14,1),(6,1),(0,1),(8,0),(1,-1),(2,1)] fam22_t63 = true := by decide +kernel

end Kalai5.LemmaA
