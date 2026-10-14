import Kalai5.LemmaA.Data.Fam15

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam15_t15_ok : fam15.walk [(8,0),(1,-1),(2,1)] fam15_t15 = true := by decide +kernel

theorem fam15_t16_ok : fam15.walk [(8,1),(1,-1),(2,1)] fam15_t16 = true := by decide +kernel

theorem fam15_t17_ok : fam15.walk [(1,0),(2,1)] fam15_t17 = true := by decide +kernel

theorem fam15_t18_ok : fam15.walk [(8,-1),(1,1),(2,1)] fam15_t18 = true := by decide +kernel

theorem fam15_t19_ok : fam15.walk [(8,0),(1,1),(2,1)] fam15_t19 = true := by decide +kernel

theorem fam15_t20_ok : fam15.walk [(0,-1),(8,1),(1,1),(2,1)] fam15_t20 = true := by decide +kernel

theorem fam15_t21_ok : fam15.walk [(0,0),(8,1),(1,1),(2,1)] fam15_t21 = true := by decide +kernel

theorem fam15_t22_ok : fam15.walk [(0,1),(8,1),(1,1),(2,1)] fam15_t22 = true := by decide +kernel

end Kalai5.LemmaA
