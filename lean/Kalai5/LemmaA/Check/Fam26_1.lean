import Kalai5.LemmaA.Data.Fam26

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam26_t5_ok : fam26.walk [(3,-1),(5,0),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t5 = true := by decide +kernel

theorem fam26_t6_ok : fam26.walk [(3,0),(5,0),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t6 = true := by decide +kernel

theorem fam26_t7_ok : fam26.walk [(3,1),(5,0),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t7 = true := by decide +kernel

theorem fam26_t8_ok : fam26.walk [(4,-1),(14,-1),(5,1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t8 = true := by decide +kernel

theorem fam26_t9_ok : fam26.walk [(4,0),(14,-1),(5,1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t9 = true := by decide +kernel

theorem fam26_t10_ok : fam26.walk [(4,1),(14,-1),(5,1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t10 = true := by decide +kernel

theorem fam26_t11_ok : fam26.walk [(14,0),(5,1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t11 = true := by decide +kernel

theorem fam26_t12_ok : fam26.walk [(14,1),(5,1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t12 = true := by decide +kernel

theorem fam26_t13_ok : fam26.walk [(6,0),(0,-1),(1,-1),(2,-1)] fam26_t13 = true := by decide +kernel

theorem fam26_t14_ok : fam26.walk [(6,1),(0,-1),(1,-1),(2,-1)] fam26_t14 = true := by decide +kernel

theorem fam26_t15_ok : fam26.walk [(0,0),(1,-1),(2,-1)] fam26_t15 = true := by decide +kernel

theorem fam26_t16_ok : fam26.walk [(3,-1),(0,1),(1,-1),(2,-1)] fam26_t16 = true := by decide +kernel

end Kalai5.LemmaA
