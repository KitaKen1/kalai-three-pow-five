import Kalai5.LemmaA.Data.Fam44

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam44_t87_ok : fam44.walk [(2,0),(5,1),(1,-1),(3,1)] fam44_t87 = true := by decide +kernel

theorem fam44_t88_ok : fam44.walk [(2,1),(5,1),(1,-1),(3,1)] fam44_t88 = true := by decide +kernel

theorem fam44_t89_ok : fam44.walk [(0,-1),(1,0),(3,1)] fam44_t89 = true := by decide +kernel

theorem fam44_t90_ok : fam44.walk [(0,0),(1,0),(3,1)] fam44_t90 = true := by decide +kernel

theorem fam44_t91_ok : fam44.walk [(5,-1),(0,1),(1,0),(3,1)] fam44_t91 = true := by decide +kernel

theorem fam44_t92_ok : fam44.walk [(5,0),(0,1),(1,0),(3,1)] fam44_t92 = true := by decide +kernel

theorem fam44_t93_ok : fam44.walk [(5,1),(0,1),(1,0),(3,1)] fam44_t93 = true := by decide +kernel

theorem fam44_t94_ok : fam44.walk [(0,-1),(1,1),(3,1)] fam44_t94 = true := by decide +kernel

theorem fam44_t95_ok : fam44.walk [(0,0),(1,1),(3,1)] fam44_t95 = true := by decide +kernel

theorem fam44_t96_ok : fam44.walk [(2,-1),(0,1),(1,1),(3,1)] fam44_t96 = true := by decide +kernel

theorem fam44_t97_ok : fam44.walk [(2,0),(0,1),(1,1),(3,1)] fam44_t97 = true := by decide +kernel

theorem fam44_t98_ok : fam44.walk [(9,-1),(2,1),(0,1),(1,1),(3,1)] fam44_t98 = true := by decide +kernel

end Kalai5.LemmaA
