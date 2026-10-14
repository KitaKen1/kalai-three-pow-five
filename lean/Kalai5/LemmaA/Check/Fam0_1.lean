import Kalai5.LemmaA.Data.Fam0

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam0_t2_ok : fam0.walk [(3,1),(1,-1),(0,-1),(2,-1)] fam0_t2 = true := by decide +kernel

theorem fam0_t3_ok : fam0.walk [(1,0),(0,-1),(2,-1)] fam0_t3 = true := by decide +kernel

theorem fam0_t4_ok : fam0.walk [(4,-1),(1,1),(0,-1),(2,-1)] fam0_t4 = true := by decide +kernel

theorem fam0_t5_ok : fam0.walk [(4,0),(1,1),(0,-1),(2,-1)] fam0_t5 = true := by decide +kernel

theorem fam0_t6_ok : fam0.walk [(4,1),(1,1),(0,-1),(2,-1)] fam0_t6 = true := by decide +kernel

theorem fam0_t7_ok : fam0.walk [(0,0),(2,-1)] fam0_t7 = true := by decide +kernel

theorem fam0_t8_ok : fam0.walk [(5,-1),(1,-1),(0,1),(2,-1)] fam0_t8 = true := by decide +kernel

theorem fam0_t9_ok : fam0.walk [(5,0),(1,-1),(0,1),(2,-1)] fam0_t9 = true := by decide +kernel

theorem fam0_t10_ok : fam0.walk [(5,1),(1,-1),(0,1),(2,-1)] fam0_t10 = true := by decide +kernel

theorem fam0_t11_ok : fam0.walk [(1,0),(0,1),(2,-1)] fam0_t11 = true := by decide +kernel

theorem fam0_t12_ok : fam0.walk [(3,-1),(1,1),(0,1),(2,-1)] fam0_t12 = true := by decide +kernel

theorem fam0_t13_ok : fam0.walk [(3,0),(1,1),(0,1),(2,-1)] fam0_t13 = true := by decide +kernel

end Kalai5.LemmaA
