import Kalai5.LemmaA.Data.Fam22

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam22_t76_ok : fam22.walk [(4,1),(0,-1),(1,1),(2,1)] fam22_t76 = true := by decide +kernel

theorem fam22_t77_ok : fam22.walk [(6,-1),(4,-1),(0,0),(1,1),(2,1)] fam22_t77 = true := by decide +kernel

theorem fam22_t78_ok : fam22.walk [(6,0),(4,-1),(0,0),(1,1),(2,1)] fam22_t78 = true := by decide +kernel

theorem fam22_t79_ok : fam22.walk [(7,-1),(6,1),(4,-1),(0,0),(1,1),(2,1)] fam22_t79 = true := by decide +kernel

theorem fam22_t80_ok : fam22.walk [(7,0),(6,1),(4,-1),(0,0),(1,1),(2,1)] fam22_t80 = true := by decide +kernel

theorem fam22_t81_ok : fam22.walk [(8,-1),(7,1),(6,1),(4,-1),(0,0),(1,1),(2,1)] fam22_t81 = true := by decide +kernel

theorem fam22_t82_ok : fam22.walk [(8,0),(7,1),(6,1),(4,-1),(0,0),(1,1),(2,1)] fam22_t82 = true := by decide +kernel

theorem fam22_t83_ok : fam22.walk [(14,-1),(8,1),(7,1),(6,1),(4,-1),(0,0),(1,1),(2,1)] fam22_t83 = true := by decide +kernel

theorem fam22_t84_ok : fam22.walk [(14,0),(8,1),(7,1),(6,1),(4,-1),(0,0),(1,1),(2,1)] fam22_t84 = true := by decide +kernel

theorem fam22_t85_ok : fam22.walk [(14,1),(8,1),(7,1),(6,1),(4,-1),(0,0),(1,1),(2,1)] fam22_t85 = true := by decide +kernel

theorem fam22_t86_ok : fam22.walk [(4,0),(0,0),(1,1),(2,1)] fam22_t86 = true := by decide +kernel

theorem fam22_t87_ok : fam22.walk [(4,1),(0,0),(1,1),(2,1)] fam22_t87 = true := by decide +kernel

end Kalai5.LemmaA
