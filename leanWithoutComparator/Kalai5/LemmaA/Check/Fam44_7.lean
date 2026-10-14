import Kalai5.LemmaA.Data.Fam44

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam44_t75_ok : fam44.walk [(0,0),(2,-1),(13,1),(4,1),(5,-1),(1,-1),(3,1)] fam44_t75 = true := by decide +kernel

theorem fam44_t76_ok : fam44.walk [(0,1),(2,-1),(13,1),(4,1),(5,-1),(1,-1),(3,1)] fam44_t76 = true := by decide +kernel

theorem fam44_t77_ok : fam44.walk [(2,0),(13,1),(4,1),(5,-1),(1,-1),(3,1)] fam44_t77 = true := by decide +kernel

theorem fam44_t78_ok : fam44.walk [(2,1),(13,1),(4,1),(5,-1),(1,-1),(3,1)] fam44_t78 = true := by decide +kernel

theorem fam44_t79_ok : fam44.walk [(5,0),(1,-1),(3,1)] fam44_t79 = true := by decide +kernel

theorem fam44_t80_ok : fam44.walk [(4,-1),(2,-1),(5,1),(1,-1),(3,1)] fam44_t80 = true := by decide +kernel

theorem fam44_t81_ok : fam44.walk [(4,0),(2,-1),(5,1),(1,-1),(3,1)] fam44_t81 = true := by decide +kernel

theorem fam44_t82_ok : fam44.walk [(13,-1),(4,1),(2,-1),(5,1),(1,-1),(3,1)] fam44_t82 = true := by decide +kernel

theorem fam44_t83_ok : fam44.walk [(13,0),(4,1),(2,-1),(5,1),(1,-1),(3,1)] fam44_t83 = true := by decide +kernel

theorem fam44_t84_ok : fam44.walk [(0,-1),(13,1),(4,1),(2,-1),(5,1),(1,-1),(3,1)] fam44_t84 = true := by decide +kernel

theorem fam44_t85_ok : fam44.walk [(0,0),(13,1),(4,1),(2,-1),(5,1),(1,-1),(3,1)] fam44_t85 = true := by decide +kernel

theorem fam44_t86_ok : fam44.walk [(0,1),(13,1),(4,1),(2,-1),(5,1),(1,-1),(3,1)] fam44_t86 = true := by decide +kernel

end Kalai5.LemmaA
