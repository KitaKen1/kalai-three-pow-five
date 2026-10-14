import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_t76_ok : fam39.walk [(1,-1),(0,1),(4,1),(3,-1),(2,1)] fam39_t76 = true := by decide +kernel

theorem fam39_t77_ok : fam39.walk [(1,0),(0,1),(4,1),(3,-1),(2,1)] fam39_t77 = true := by decide +kernel

theorem fam39_t78_ok : fam39.walk [(5,-1),(1,1),(0,1),(4,1),(3,-1),(2,1)] fam39_t78 = true := by decide +kernel

theorem fam39_t79_ok : fam39.walk [(5,0),(1,1),(0,1),(4,1),(3,-1),(2,1)] fam39_t79 = true := by decide +kernel

theorem fam39_t80_ok : fam39.walk [(10,-1),(5,1),(1,1),(0,1),(4,1),(3,-1),(2,1)] fam39_t80 = true := by decide +kernel

theorem fam39_t81_ok : fam39.walk [(10,0),(5,1),(1,1),(0,1),(4,1),(3,-1),(2,1)] fam39_t81 = true := by decide +kernel

theorem fam39_t82_ok : fam39.walk [(10,1),(5,1),(1,1),(0,1),(4,1),(3,-1),(2,1)] fam39_t82 = true := by decide +kernel

theorem fam39_t83_ok : fam39.walk [(9,-1),(3,0),(2,1)] fam39_t83 = true := by decide +kernel

theorem fam39_t84_ok : fam39.walk [(9,0),(3,0),(2,1)] fam39_t84 = true := by decide +kernel

theorem fam39_t85_ok : fam39.walk [(0,-1),(11,-1),(9,1),(3,0),(2,1)] fam39_t85 = true := by decide +kernel

theorem fam39_t86_ok : fam39.walk [(0,0),(11,-1),(9,1),(3,0),(2,1)] fam39_t86 = true := by decide +kernel

theorem fam39_t87_ok : fam39.walk [(1,-1),(0,1),(11,-1),(9,1),(3,0),(2,1)] fam39_t87 = true := by decide +kernel

end Kalai5.LemmaA
