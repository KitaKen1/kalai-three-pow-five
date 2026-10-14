import Kalai5.LemmaA.Data.Fam15

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam15_t3_ok : fam15.walk [(8,0),(1,-1),(2,-1)] fam15_t3 = true := by decide +kernel

theorem fam15_t4_ok : fam15.walk [(8,1),(1,-1),(2,-1)] fam15_t4 = true := by decide +kernel

theorem fam15_t5_ok : fam15.walk [(1,0),(2,-1)] fam15_t5 = true := by decide +kernel

theorem fam15_t6_ok : fam15.walk [(8,-1),(1,1),(2,-1)] fam15_t6 = true := by decide +kernel

theorem fam15_t7_ok : fam15.walk [(8,0),(1,1),(2,-1)] fam15_t7 = true := by decide +kernel

theorem fam15_t8_ok : fam15.walk [(0,-1),(8,1),(1,1),(2,-1)] fam15_t8 = true := by decide +kernel

theorem fam15_t9_ok : fam15.walk [(0,0),(8,1),(1,1),(2,-1)] fam15_t9 = true := by decide +kernel

theorem fam15_t10_ok : fam15.walk [(0,1),(8,1),(1,1),(2,-1)] fam15_t10 = true := by decide +kernel

theorem fam15_t11_ok : fam15.walk [(2,0)] fam15_t11 = true := by decide +kernel

theorem fam15_t12_ok : fam15.walk [(0,-1),(8,-1),(1,-1),(2,1)] fam15_t12 = true := by decide +kernel

theorem fam15_t13_ok : fam15.walk [(0,0),(8,-1),(1,-1),(2,1)] fam15_t13 = true := by decide +kernel

theorem fam15_t14_ok : fam15.walk [(0,1),(8,-1),(1,-1),(2,1)] fam15_t14 = true := by decide +kernel

end Kalai5.LemmaA
