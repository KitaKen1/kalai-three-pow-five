import Kalai5.LemmaA.Data.Fam32

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam32_t62_ok : fam32.walk [(8,-1),(7,-1),(0,-1),(1,-1),(3,1),(2,1)] fam32_t62 = true := by decide +kernel

theorem fam32_t63_ok : fam32.walk [(8,0),(7,-1),(0,-1),(1,-1),(3,1),(2,1)] fam32_t63 = true := by decide +kernel

theorem fam32_t64_ok : fam32.walk [(8,1),(7,-1),(0,-1),(1,-1),(3,1),(2,1)] fam32_t64 = true := by decide +kernel

theorem fam32_t65_ok : fam32.walk [(7,0),(0,-1),(1,-1),(3,1),(2,1)] fam32_t65 = true := by decide +kernel

theorem fam32_t66_ok : fam32.walk [(7,1),(0,-1),(1,-1),(3,1),(2,1)] fam32_t66 = true := by decide +kernel

theorem fam32_t67_ok : fam32.walk [(0,0),(1,-1),(3,1),(2,1)] fam32_t67 = true := by decide +kernel

theorem fam32_t68_ok : fam32.walk [(8,-1),(0,1),(1,-1),(3,1),(2,1)] fam32_t68 = true := by decide +kernel

theorem fam32_t69_ok : fam32.walk [(8,0),(0,1),(1,-1),(3,1),(2,1)] fam32_t69 = true := by decide +kernel

theorem fam32_t70_ok : fam32.walk [(7,-1),(8,1),(0,1),(1,-1),(3,1),(2,1)] fam32_t70 = true := by decide +kernel

theorem fam32_t71_ok : fam32.walk [(7,0),(8,1),(0,1),(1,-1),(3,1),(2,1)] fam32_t71 = true := by decide +kernel

theorem fam32_t72_ok : fam32.walk [(7,1),(8,1),(0,1),(1,-1),(3,1),(2,1)] fam32_t72 = true := by decide +kernel

theorem fam32_t73_ok : fam32.walk [(1,0),(3,1),(2,1)] fam32_t73 = true := by decide +kernel

end Kalai5.LemmaA
