import Kalai5.LemmaA.Data.Fam12

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam12_t2_ok : fam12.walk [(5,1),(8,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam12_t2 = true := by decide +kernel

theorem fam12_t3_ok : fam12.walk [(8,0),(6,-1),(0,-1),(1,-1),(2,-1)] fam12_t3 = true := by decide +kernel

theorem fam12_t4_ok : fam12.walk [(8,1),(6,-1),(0,-1),(1,-1),(2,-1)] fam12_t4 = true := by decide +kernel

theorem fam12_t5_ok : fam12.walk [(6,0),(0,-1),(1,-1),(2,-1)] fam12_t5 = true := by decide +kernel

theorem fam12_t6_ok : fam12.walk [(6,1),(0,-1),(1,-1),(2,-1)] fam12_t6 = true := by decide +kernel

theorem fam12_t7_ok : fam12.walk [(0,0),(1,-1),(2,-1)] fam12_t7 = true := by decide +kernel

theorem fam12_t8_ok : fam12.walk [(4,-1),(0,1),(1,-1),(2,-1)] fam12_t8 = true := by decide +kernel

theorem fam12_t9_ok : fam12.walk [(4,0),(0,1),(1,-1),(2,-1)] fam12_t9 = true := by decide +kernel

theorem fam12_t10_ok : fam12.walk [(8,-1),(4,1),(0,1),(1,-1),(2,-1)] fam12_t10 = true := by decide +kernel

theorem fam12_t11_ok : fam12.walk [(8,0),(4,1),(0,1),(1,-1),(2,-1)] fam12_t11 = true := by decide +kernel

theorem fam12_t12_ok : fam12.walk [(5,-1),(8,1),(4,1),(0,1),(1,-1),(2,-1)] fam12_t12 = true := by decide +kernel

theorem fam12_t13_ok : fam12.walk [(5,0),(8,1),(4,1),(0,1),(1,-1),(2,-1)] fam12_t13 = true := by decide +kernel

end Kalai5.LemmaA
