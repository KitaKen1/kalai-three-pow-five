import Kalai5.LemmaA.Data.Fam26

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam26_t65_ok : fam26.walk [(11,0),(4,-1),(1,-1),(2,1)] fam26_t65 = true := by decide +kernel

theorem fam26_t66_ok : fam26.walk [(11,1),(4,-1),(1,-1),(2,1)] fam26_t66 = true := by decide +kernel

theorem fam26_t67_ok : fam26.walk [(4,0),(1,-1),(2,1)] fam26_t67 = true := by decide +kernel

theorem fam26_t68_ok : fam26.walk [(0,-1),(4,1),(1,-1),(2,1)] fam26_t68 = true := by decide +kernel

theorem fam26_t69_ok : fam26.walk [(0,0),(4,1),(1,-1),(2,1)] fam26_t69 = true := by decide +kernel

theorem fam26_t70_ok : fam26.walk [(3,-1),(0,1),(4,1),(1,-1),(2,1)] fam26_t70 = true := by decide +kernel

theorem fam26_t71_ok : fam26.walk [(3,0),(0,1),(4,1),(1,-1),(2,1)] fam26_t71 = true := by decide +kernel

theorem fam26_t72_ok : fam26.walk [(10,-1),(3,1),(0,1),(4,1),(1,-1),(2,1)] fam26_t72 = true := by decide +kernel

theorem fam26_t73_ok : fam26.walk [(10,0),(3,1),(0,1),(4,1),(1,-1),(2,1)] fam26_t73 = true := by decide +kernel

theorem fam26_t74_ok : fam26.walk [(6,-1),(10,1),(3,1),(0,1),(4,1),(1,-1),(2,1)] fam26_t74 = true := by decide +kernel

theorem fam26_t75_ok : fam26.walk [(6,0),(10,1),(3,1),(0,1),(4,1),(1,-1),(2,1)] fam26_t75 = true := by decide +kernel

theorem fam26_t76_ok : fam26.walk [(6,1),(10,1),(3,1),(0,1),(4,1),(1,-1),(2,1)] fam26_t76 = true := by decide +kernel

end Kalai5.LemmaA
