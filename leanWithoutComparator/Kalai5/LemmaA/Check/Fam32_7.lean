import Kalai5.LemmaA.Data.Fam32

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam32_t74_ok : fam32.walk [(1,1),(3,1),(2,1)] fam32_t74 = true := by decide +kernel

end Kalai5.LemmaA
