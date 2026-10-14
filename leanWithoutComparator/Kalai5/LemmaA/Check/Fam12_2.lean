import Kalai5.LemmaA.Data.Fam12

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam12_t14_ok : fam12.walk [(5,1),(8,1),(4,1),(0,1),(1,-1),(2,-1)] fam12_t14 = true := by decide +kernel

theorem fam12_t15_ok : fam12.walk [(1,0),(2,-1)] fam12_t15 = true := by decide +kernel

theorem fam12_t16_ok : fam12.walk [(9,-1),(4,-1),(0,-1),(6,-1),(1,1),(2,-1)] fam12_t16 = true := by decide +kernel

theorem fam12_t17_ok : fam12.walk [(9,0),(4,-1),(0,-1),(6,-1),(1,1),(2,-1)] fam12_t17 = true := by decide +kernel

theorem fam12_t18_ok : fam12.walk [(9,1),(4,-1),(0,-1),(6,-1),(1,1),(2,-1)] fam12_t18 = true := by decide +kernel

theorem fam12_t19_ok : fam12.walk [(4,0),(0,-1),(6,-1),(1,1),(2,-1)] fam12_t19 = true := by decide +kernel

theorem fam12_t20_ok : fam12.walk [(4,1),(0,-1),(6,-1),(1,1),(2,-1)] fam12_t20 = true := by decide +kernel

theorem fam12_t21_ok : fam12.walk [(0,0),(6,-1),(1,1),(2,-1)] fam12_t21 = true := by decide +kernel

theorem fam12_t22_ok : fam12.walk [(0,1),(6,-1),(1,1),(2,-1)] fam12_t22 = true := by decide +kernel

theorem fam12_t23_ok : fam12.walk [(6,0),(1,1),(2,-1)] fam12_t23 = true := by decide +kernel

theorem fam12_t24_ok : fam12.walk [(8,-1),(6,1),(1,1),(2,-1)] fam12_t24 = true := by decide +kernel

theorem fam12_t25_ok : fam12.walk [(8,0),(6,1),(1,1),(2,-1)] fam12_t25 = true := by decide +kernel

end Kalai5.LemmaA
