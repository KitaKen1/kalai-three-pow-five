import Kalai5.LemmaA.Data.Fam0

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam0_t26_ok : fam0.walk [(4,1),(1,-1),(0,1),(2,1)] fam0_t26 = true := by decide +kernel

theorem fam0_t27_ok : fam0.walk [(1,0),(0,1),(2,1)] fam0_t27 = true := by decide +kernel

theorem fam0_t28_ok : fam0.walk [(3,-1),(1,1),(0,1),(2,1)] fam0_t28 = true := by decide +kernel

theorem fam0_t29_ok : fam0.walk [(3,0),(1,1),(0,1),(2,1)] fam0_t29 = true := by decide +kernel

theorem fam0_t30_ok : fam0.walk [(3,1),(1,1),(0,1),(2,1)] fam0_t30 = true := by decide +kernel

end Kalai5.LemmaA
