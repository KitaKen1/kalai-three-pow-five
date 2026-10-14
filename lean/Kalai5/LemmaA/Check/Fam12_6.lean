import Kalai5.LemmaA.Data.Fam12

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam12_t62_ok : fam12.walk [(5,1),(8,1),(6,1),(0,1),(1,1),(2,1)] fam12_t62 = true := by decide +kernel

end Kalai5.LemmaA
