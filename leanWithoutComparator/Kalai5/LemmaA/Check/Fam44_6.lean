import Kalai5.LemmaA.Data.Fam44

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam44_t63_ok : fam44.walk [(7,0),(4,-1),(5,-1),(1,-1),(3,1)] fam44_t63 = true := by decide +kernel

theorem fam44_t64_ok : fam44.walk [(7,1),(4,-1),(5,-1),(1,-1),(3,1)] fam44_t64 = true := by decide +kernel

theorem fam44_t65_ok : fam44.walk [(13,-1),(7,-1),(4,0),(5,-1),(1,-1),(3,1)] fam44_t65 = true := by decide +kernel

theorem fam44_t66_ok : fam44.walk [(13,0),(7,-1),(4,0),(5,-1),(1,-1),(3,1)] fam44_t66 = true := by decide +kernel

theorem fam44_t67_ok : fam44.walk [(0,-1),(13,1),(7,-1),(4,0),(5,-1),(1,-1),(3,1)] fam44_t67 = true := by decide +kernel

theorem fam44_t68_ok : fam44.walk [(0,0),(13,1),(7,-1),(4,0),(5,-1),(1,-1),(3,1)] fam44_t68 = true := by decide +kernel

theorem fam44_t69_ok : fam44.walk [(0,1),(13,1),(7,-1),(4,0),(5,-1),(1,-1),(3,1)] fam44_t69 = true := by decide +kernel

theorem fam44_t70_ok : fam44.walk [(7,0),(4,0),(5,-1),(1,-1),(3,1)] fam44_t70 = true := by decide +kernel

theorem fam44_t71_ok : fam44.walk [(7,1),(4,0),(5,-1),(1,-1),(3,1)] fam44_t71 = true := by decide +kernel

theorem fam44_t72_ok : fam44.walk [(13,-1),(4,1),(5,-1),(1,-1),(3,1)] fam44_t72 = true := by decide +kernel

theorem fam44_t73_ok : fam44.walk [(13,0),(4,1),(5,-1),(1,-1),(3,1)] fam44_t73 = true := by decide +kernel

theorem fam44_t74_ok : fam44.walk [(0,-1),(2,-1),(13,1),(4,1),(5,-1),(1,-1),(3,1)] fam44_t74 = true := by decide +kernel

end Kalai5.LemmaA
