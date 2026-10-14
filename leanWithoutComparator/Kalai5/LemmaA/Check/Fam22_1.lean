import Kalai5.LemmaA.Data.Fam22

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam22_t4_ok : fam22.walk [(8,1),(6,-1),(0,-1),(1,-1),(2,-1)] fam22_t4 = true := by decide +kernel

theorem fam22_t5_ok : fam22.walk [(6,0),(0,-1),(1,-1),(2,-1)] fam22_t5 = true := by decide +kernel

theorem fam22_t6_ok : fam22.walk [(6,1),(0,-1),(1,-1),(2,-1)] fam22_t6 = true := by decide +kernel

theorem fam22_t7_ok : fam22.walk [(4,-1),(0,0),(1,-1),(2,-1)] fam22_t7 = true := by decide +kernel

theorem fam22_t8_ok : fam22.walk [(4,0),(0,0),(1,-1),(2,-1)] fam22_t8 = true := by decide +kernel

theorem fam22_t9_ok : fam22.walk [(14,-1),(8,-1),(7,-1),(6,-1),(4,1),(0,0),(1,-1),(2,-1)] fam22_t9 = true := by decide +kernel

theorem fam22_t10_ok : fam22.walk [(14,0),(8,-1),(7,-1),(6,-1),(4,1),(0,0),(1,-1),(2,-1)] fam22_t10 = true := by decide +kernel

theorem fam22_t11_ok : fam22.walk [(14,1),(8,-1),(7,-1),(6,-1),(4,1),(0,0),(1,-1),(2,-1)] fam22_t11 = true := by decide +kernel

theorem fam22_t12_ok : fam22.walk [(8,0),(7,-1),(6,-1),(4,1),(0,0),(1,-1),(2,-1)] fam22_t12 = true := by decide +kernel

theorem fam22_t13_ok : fam22.walk [(8,1),(7,-1),(6,-1),(4,1),(0,0),(1,-1),(2,-1)] fam22_t13 = true := by decide +kernel

theorem fam22_t14_ok : fam22.walk [(7,0),(6,-1),(4,1),(0,0),(1,-1),(2,-1)] fam22_t14 = true := by decide +kernel

theorem fam22_t15_ok : fam22.walk [(7,1),(6,-1),(4,1),(0,0),(1,-1),(2,-1)] fam22_t15 = true := by decide +kernel

end Kalai5.LemmaA
