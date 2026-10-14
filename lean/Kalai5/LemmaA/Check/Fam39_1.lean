import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_t4_ok : fam39.walk [(14,1),(10,-1),(0,-1),(4,-1),(3,-1),(2,-1)] fam39_t4 = true := by decide +kernel

theorem fam39_t5_ok : fam39.walk [(10,0),(0,-1),(4,-1),(3,-1),(2,-1)] fam39_t5 = true := by decide +kernel

theorem fam39_t6_ok : fam39.walk [(10,1),(0,-1),(4,-1),(3,-1),(2,-1)] fam39_t6 = true := by decide +kernel

theorem fam39_t7_ok : fam39.walk [(0,0),(4,-1),(3,-1),(2,-1)] fam39_t7 = true := by decide +kernel

theorem fam39_t8_ok : fam39.walk [(0,1),(4,-1),(3,-1),(2,-1)] fam39_t8 = true := by decide +kernel

theorem fam39_t9_ok : fam39.walk [(4,0),(3,-1),(2,-1)] fam39_t9 = true := by decide +kernel

theorem fam39_t10_ok : fam39.walk [(5,-1),(4,1),(3,-1),(2,-1)] fam39_t10 = true := by decide +kernel

theorem fam39_t11_ok : fam39.walk [(5,0),(4,1),(3,-1),(2,-1)] fam39_t11 = true := by decide +kernel

theorem fam39_t12_ok : fam39.walk [(1,-1),(10,-1),(0,-1),(5,1),(4,1),(3,-1),(2,-1)] fam39_t12 = true := by decide +kernel

theorem fam39_t13_ok : fam39.walk [(1,0),(10,-1),(0,-1),(5,1),(4,1),(3,-1),(2,-1)] fam39_t13 = true := by decide +kernel

theorem fam39_t14_ok : fam39.walk [(1,1),(10,-1),(0,-1),(5,1),(4,1),(3,-1),(2,-1)] fam39_t14 = true := by decide +kernel

theorem fam39_t15_ok : fam39.walk [(10,0),(0,-1),(5,1),(4,1),(3,-1),(2,-1)] fam39_t15 = true := by decide +kernel

end Kalai5.LemmaA
