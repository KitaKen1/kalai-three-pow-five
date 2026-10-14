import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_t64_ok : fam39.walk [(10,1),(0,-1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t64 = true := by decide +kernel

theorem fam39_t65_ok : fam39.walk [(0,0),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t65 = true := by decide +kernel

theorem fam39_t66_ok : fam39.walk [(1,-1),(0,1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t66 = true := by decide +kernel

theorem fam39_t67_ok : fam39.walk [(1,0),(0,1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t67 = true := by decide +kernel

theorem fam39_t68_ok : fam39.walk [(5,-1),(1,1),(0,1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t68 = true := by decide +kernel

theorem fam39_t69_ok : fam39.walk [(5,0),(1,1),(0,1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t69 = true := by decide +kernel

theorem fam39_t70_ok : fam39.walk [(5,1),(1,1),(0,1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_t70 = true := by decide +kernel

theorem fam39_t71_ok : fam39.walk [(14,0),(4,-1),(3,-1),(2,1)] fam39_t71 = true := by decide +kernel

theorem fam39_t72_ok : fam39.walk [(14,1),(4,-1),(3,-1),(2,1)] fam39_t72 = true := by decide +kernel

theorem fam39_t73_ok : fam39.walk [(4,0),(3,-1),(2,1)] fam39_t73 = true := by decide +kernel

theorem fam39_t74_ok : fam39.walk [(0,-1),(4,1),(3,-1),(2,1)] fam39_t74 = true := by decide +kernel

theorem fam39_t75_ok : fam39.walk [(0,0),(4,1),(3,-1),(2,1)] fam39_t75 = true := by decide +kernel

end Kalai5.LemmaA
