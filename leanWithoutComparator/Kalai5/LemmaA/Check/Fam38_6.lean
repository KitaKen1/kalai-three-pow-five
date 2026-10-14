import Kalai5.LemmaA.Data.Fam38

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam38_t64_ok : fam38.walk [(1,0),(0,-1),(11,-1),(3,0),(2,1)] fam38_t64 = true := by decide +kernel

theorem fam38_t65_ok : fam38.walk [(1,1),(0,-1),(11,-1),(3,0),(2,1)] fam38_t65 = true := by decide +kernel

theorem fam38_t66_ok : fam38.walk [(0,0),(11,-1),(3,0),(2,1)] fam38_t66 = true := by decide +kernel

theorem fam38_t67_ok : fam38.walk [(0,1),(11,-1),(3,0),(2,1)] fam38_t67 = true := by decide +kernel

theorem fam38_t68_ok : fam38.walk [(11,0),(3,0),(2,1)] fam38_t68 = true := by decide +kernel

theorem fam38_t69_ok : fam38.walk [(11,1),(3,0),(2,1)] fam38_t69 = true := by decide +kernel

theorem fam38_t70_ok : fam38.walk [(8,-1),(1,-1),(0,-1),(3,1),(2,1)] fam38_t70 = true := by decide +kernel

theorem fam38_t71_ok : fam38.walk [(8,0),(1,-1),(0,-1),(3,1),(2,1)] fam38_t71 = true := by decide +kernel

theorem fam38_t72_ok : fam38.walk [(11,-1),(8,1),(1,-1),(0,-1),(3,1),(2,1)] fam38_t72 = true := by decide +kernel

theorem fam38_t73_ok : fam38.walk [(11,0),(8,1),(1,-1),(0,-1),(3,1),(2,1)] fam38_t73 = true := by decide +kernel

theorem fam38_t74_ok : fam38.walk [(11,1),(8,1),(1,-1),(0,-1),(3,1),(2,1)] fam38_t74 = true := by decide +kernel

theorem fam38_t75_ok : fam38.walk [(1,0),(0,-1),(3,1),(2,1)] fam38_t75 = true := by decide +kernel

end Kalai5.LemmaA
