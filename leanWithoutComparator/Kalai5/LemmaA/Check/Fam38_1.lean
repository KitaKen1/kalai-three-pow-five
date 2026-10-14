import Kalai5.LemmaA.Data.Fam38

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam38_t4_ok : fam38.walk [(11,1),(10,-1),(8,-1),(0,-1),(3,-1),(2,-1)] fam38_t4 = true := by decide +kernel

theorem fam38_t5_ok : fam38.walk [(10,0),(8,-1),(0,-1),(3,-1),(2,-1)] fam38_t5 = true := by decide +kernel

theorem fam38_t6_ok : fam38.walk [(10,1),(8,-1),(0,-1),(3,-1),(2,-1)] fam38_t6 = true := by decide +kernel

theorem fam38_t7_ok : fam38.walk [(8,0),(0,-1),(3,-1),(2,-1)] fam38_t7 = true := by decide +kernel

theorem fam38_t8_ok : fam38.walk [(8,1),(0,-1),(3,-1),(2,-1)] fam38_t8 = true := by decide +kernel

theorem fam38_t9_ok : fam38.walk [(1,-1),(0,0),(3,-1),(2,-1)] fam38_t9 = true := by decide +kernel

theorem fam38_t10_ok : fam38.walk [(1,0),(0,0),(3,-1),(2,-1)] fam38_t10 = true := by decide +kernel

theorem fam38_t11_ok : fam38.walk [(11,-1),(10,-1),(8,-1),(1,1),(0,0),(3,-1),(2,-1)] fam38_t11 = true := by decide +kernel

theorem fam38_t12_ok : fam38.walk [(11,0),(10,-1),(8,-1),(1,1),(0,0),(3,-1),(2,-1)] fam38_t12 = true := by decide +kernel

theorem fam38_t13_ok : fam38.walk [(11,1),(10,-1),(8,-1),(1,1),(0,0),(3,-1),(2,-1)] fam38_t13 = true := by decide +kernel

theorem fam38_t14_ok : fam38.walk [(10,0),(8,-1),(1,1),(0,0),(3,-1),(2,-1)] fam38_t14 = true := by decide +kernel

theorem fam38_t15_ok : fam38.walk [(10,1),(8,-1),(1,1),(0,0),(3,-1),(2,-1)] fam38_t15 = true := by decide +kernel

end Kalai5.LemmaA
