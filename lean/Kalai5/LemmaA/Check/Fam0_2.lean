import Kalai5.LemmaA.Data.Fam0

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam0_t14_ok : fam0.walk [(3,1),(1,1),(0,1),(2,-1)] fam0_t14 = true := by decide +kernel

theorem fam0_t15_ok : fam0.walk [(2,0)] fam0_t15 = true := by decide +kernel

theorem fam0_t16_ok : fam0.walk [(3,-1),(1,-1),(0,-1),(2,1)] fam0_t16 = true := by decide +kernel

theorem fam0_t17_ok : fam0.walk [(3,0),(1,-1),(0,-1),(2,1)] fam0_t17 = true := by decide +kernel

theorem fam0_t18_ok : fam0.walk [(3,1),(1,-1),(0,-1),(2,1)] fam0_t18 = true := by decide +kernel

theorem fam0_t19_ok : fam0.walk [(1,0),(0,-1),(2,1)] fam0_t19 = true := by decide +kernel

theorem fam0_t20_ok : fam0.walk [(5,-1),(1,1),(0,-1),(2,1)] fam0_t20 = true := by decide +kernel

theorem fam0_t21_ok : fam0.walk [(5,0),(1,1),(0,-1),(2,1)] fam0_t21 = true := by decide +kernel

theorem fam0_t22_ok : fam0.walk [(5,1),(1,1),(0,-1),(2,1)] fam0_t22 = true := by decide +kernel

theorem fam0_t23_ok : fam0.walk [(0,0),(2,1)] fam0_t23 = true := by decide +kernel

theorem fam0_t24_ok : fam0.walk [(4,-1),(1,-1),(0,1),(2,1)] fam0_t24 = true := by decide +kernel

theorem fam0_t25_ok : fam0.walk [(4,0),(1,-1),(0,1),(2,1)] fam0_t25 = true := by decide +kernel

end Kalai5.LemmaA
