import Kalai5.LemmaA.Data.Fam44

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam44_t99_ok : fam44.walk [(9,0),(2,1),(0,1),(1,1),(3,1)] fam44_t99 = true := by decide +kernel

theorem fam44_t100_ok : fam44.walk [(4,-1),(5,-1),(9,1),(2,1),(0,1),(1,1),(3,1)] fam44_t100 = true := by decide +kernel

theorem fam44_t101_ok : fam44.walk [(4,0),(5,-1),(9,1),(2,1),(0,1),(1,1),(3,1)] fam44_t101 = true := by decide +kernel

theorem fam44_t102_ok : fam44.walk [(4,1),(5,-1),(9,1),(2,1),(0,1),(1,1),(3,1)] fam44_t102 = true := by decide +kernel

theorem fam44_t103_ok : fam44.walk [(5,0),(9,1),(2,1),(0,1),(1,1),(3,1)] fam44_t103 = true := by decide +kernel

theorem fam44_t104_ok : fam44.walk [(5,1),(9,1),(2,1),(0,1),(1,1),(3,1)] fam44_t104 = true := by decide +kernel

end Kalai5.LemmaA
