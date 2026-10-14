import Kalai5.LemmaA.Data.Fam26

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam26_t77_ok : fam26.walk [(1,0),(2,1)] fam26_t77 = true := by decide +kernel

theorem fam26_t78_ok : fam26.walk [(8,-1),(10,-1),(4,-1),(3,-1),(0,-1),(1,1),(2,1)] fam26_t78 = true := by decide +kernel

theorem fam26_t79_ok : fam26.walk [(8,0),(10,-1),(4,-1),(3,-1),(0,-1),(1,1),(2,1)] fam26_t79 = true := by decide +kernel

theorem fam26_t80_ok : fam26.walk [(8,1),(10,-1),(4,-1),(3,-1),(0,-1),(1,1),(2,1)] fam26_t80 = true := by decide +kernel

theorem fam26_t81_ok : fam26.walk [(10,0),(4,-1),(3,-1),(0,-1),(1,1),(2,1)] fam26_t81 = true := by decide +kernel

theorem fam26_t82_ok : fam26.walk [(10,1),(4,-1),(3,-1),(0,-1),(1,1),(2,1)] fam26_t82 = true := by decide +kernel

theorem fam26_t83_ok : fam26.walk [(4,0),(3,-1),(0,-1),(1,1),(2,1)] fam26_t83 = true := by decide +kernel

theorem fam26_t84_ok : fam26.walk [(4,1),(3,-1),(0,-1),(1,1),(2,1)] fam26_t84 = true := by decide +kernel

theorem fam26_t85_ok : fam26.walk [(3,0),(0,-1),(1,1),(2,1)] fam26_t85 = true := by decide +kernel

theorem fam26_t86_ok : fam26.walk [(3,1),(0,-1),(1,1),(2,1)] fam26_t86 = true := by decide +kernel

theorem fam26_t87_ok : fam26.walk [(0,0),(1,1),(2,1)] fam26_t87 = true := by decide +kernel

theorem fam26_t88_ok : fam26.walk [(6,-1),(0,1),(1,1),(2,1)] fam26_t88 = true := by decide +kernel

end Kalai5.LemmaA
