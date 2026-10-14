import Kalai5.LemmaA.Data.Fam26

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam26_t101_ok : fam26.walk [(3,0),(8,1),(5,1),(6,1),(0,1),(1,1),(2,1)] fam26_t101 = true := by decide +kernel

theorem fam26_t102_ok : fam26.walk [(3,1),(8,1),(5,1),(6,1),(0,1),(1,1),(2,1)] fam26_t102 = true := by decide +kernel

end Kalai5.LemmaA
