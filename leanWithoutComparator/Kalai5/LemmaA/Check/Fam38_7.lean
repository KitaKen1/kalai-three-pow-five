import Kalai5.LemmaA.Data.Fam38

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam38_t76_ok : fam38.walk [(1,1),(0,-1),(3,1),(2,1)] fam38_t76 = true := by decide +kernel

theorem fam38_t77_ok : fam38.walk [(8,-1),(1,-1),(0,0),(3,1),(2,1)] fam38_t77 = true := by decide +kernel

theorem fam38_t78_ok : fam38.walk [(8,0),(1,-1),(0,0),(3,1),(2,1)] fam38_t78 = true := by decide +kernel

theorem fam38_t79_ok : fam38.walk [(10,-1),(8,1),(1,-1),(0,0),(3,1),(2,1)] fam38_t79 = true := by decide +kernel

theorem fam38_t80_ok : fam38.walk [(10,0),(8,1),(1,-1),(0,0),(3,1),(2,1)] fam38_t80 = true := by decide +kernel

theorem fam38_t81_ok : fam38.walk [(11,-1),(10,1),(8,1),(1,-1),(0,0),(3,1),(2,1)] fam38_t81 = true := by decide +kernel

theorem fam38_t82_ok : fam38.walk [(11,0),(10,1),(8,1),(1,-1),(0,0),(3,1),(2,1)] fam38_t82 = true := by decide +kernel

theorem fam38_t83_ok : fam38.walk [(11,1),(10,1),(8,1),(1,-1),(0,0),(3,1),(2,1)] fam38_t83 = true := by decide +kernel

theorem fam38_t84_ok : fam38.walk [(1,0),(0,0),(3,1),(2,1)] fam38_t84 = true := by decide +kernel

theorem fam38_t85_ok : fam38.walk [(1,1),(0,0),(3,1),(2,1)] fam38_t85 = true := by decide +kernel

theorem fam38_t86_ok : fam38.walk [(8,-1),(0,1),(3,1),(2,1)] fam38_t86 = true := by decide +kernel

theorem fam38_t87_ok : fam38.walk [(8,0),(0,1),(3,1),(2,1)] fam38_t87 = true := by decide +kernel

end Kalai5.LemmaA
