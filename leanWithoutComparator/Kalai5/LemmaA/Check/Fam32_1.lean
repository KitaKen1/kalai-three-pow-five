import Kalai5.LemmaA.Data.Fam32

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam32_t2_ok : fam32.walk [(7,-1),(8,-1),(0,-1),(1,1),(3,-1),(2,-1)] fam32_t2 = true := by decide +kernel

theorem fam32_t3_ok : fam32.walk [(7,0),(8,-1),(0,-1),(1,1),(3,-1),(2,-1)] fam32_t3 = true := by decide +kernel

theorem fam32_t4_ok : fam32.walk [(7,1),(8,-1),(0,-1),(1,1),(3,-1),(2,-1)] fam32_t4 = true := by decide +kernel

theorem fam32_t5_ok : fam32.walk [(8,0),(0,-1),(1,1),(3,-1),(2,-1)] fam32_t5 = true := by decide +kernel

theorem fam32_t6_ok : fam32.walk [(8,1),(0,-1),(1,1),(3,-1),(2,-1)] fam32_t6 = true := by decide +kernel

theorem fam32_t7_ok : fam32.walk [(0,0),(1,1),(3,-1),(2,-1)] fam32_t7 = true := by decide +kernel

theorem fam32_t8_ok : fam32.walk [(7,-1),(0,1),(1,1),(3,-1),(2,-1)] fam32_t8 = true := by decide +kernel

theorem fam32_t9_ok : fam32.walk [(7,0),(0,1),(1,1),(3,-1),(2,-1)] fam32_t9 = true := by decide +kernel

theorem fam32_t10_ok : fam32.walk [(8,-1),(7,1),(0,1),(1,1),(3,-1),(2,-1)] fam32_t10 = true := by decide +kernel

theorem fam32_t11_ok : fam32.walk [(8,0),(7,1),(0,1),(1,1),(3,-1),(2,-1)] fam32_t11 = true := by decide +kernel

theorem fam32_t12_ok : fam32.walk [(8,1),(7,1),(0,1),(1,1),(3,-1),(2,-1)] fam32_t12 = true := by decide +kernel

theorem fam32_t13_ok : fam32.walk [(0,-1),(9,-1),(3,0),(2,-1)] fam32_t13 = true := by decide +kernel

end Kalai5.LemmaA
