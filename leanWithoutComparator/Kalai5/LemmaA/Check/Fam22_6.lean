import Kalai5.LemmaA.Data.Fam22

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam22_t64_ok : fam22.walk [(0,-1),(8,1),(1,-1),(2,1)] fam22_t64 = true := by decide +kernel

theorem fam22_t65_ok : fam22.walk [(0,0),(8,1),(1,-1),(2,1)] fam22_t65 = true := by decide +kernel

theorem fam22_t66_ok : fam22.walk [(6,-1),(0,1),(8,1),(1,-1),(2,1)] fam22_t66 = true := by decide +kernel

theorem fam22_t67_ok : fam22.walk [(6,0),(0,1),(8,1),(1,-1),(2,1)] fam22_t67 = true := by decide +kernel

theorem fam22_t68_ok : fam22.walk [(4,-1),(6,1),(0,1),(8,1),(1,-1),(2,1)] fam22_t68 = true := by decide +kernel

theorem fam22_t69_ok : fam22.walk [(4,0),(6,1),(0,1),(8,1),(1,-1),(2,1)] fam22_t69 = true := by decide +kernel

theorem fam22_t70_ok : fam22.walk [(4,1),(6,1),(0,1),(8,1),(1,-1),(2,1)] fam22_t70 = true := by decide +kernel

theorem fam22_t71_ok : fam22.walk [(1,0),(2,1)] fam22_t71 = true := by decide +kernel

theorem fam22_t72_ok : fam22.walk [(5,-1),(4,-1),(0,-1),(1,1),(2,1)] fam22_t72 = true := by decide +kernel

theorem fam22_t73_ok : fam22.walk [(5,0),(4,-1),(0,-1),(1,1),(2,1)] fam22_t73 = true := by decide +kernel

theorem fam22_t74_ok : fam22.walk [(5,1),(4,-1),(0,-1),(1,1),(2,1)] fam22_t74 = true := by decide +kernel

theorem fam22_t75_ok : fam22.walk [(4,0),(0,-1),(1,1),(2,1)] fam22_t75 = true := by decide +kernel

end Kalai5.LemmaA
