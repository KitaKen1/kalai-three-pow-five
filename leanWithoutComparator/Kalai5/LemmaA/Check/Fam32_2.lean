import Kalai5.LemmaA.Data.Fam32

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam32_t14_ok : fam32.walk [(0,0),(9,-1),(3,0),(2,-1)] fam32_t14 = true := by decide +kernel

theorem fam32_t15_ok : fam32.walk [(1,-1),(0,1),(9,-1),(3,0),(2,-1)] fam32_t15 = true := by decide +kernel

theorem fam32_t16_ok : fam32.walk [(1,0),(0,1),(9,-1),(3,0),(2,-1)] fam32_t16 = true := by decide +kernel

theorem fam32_t17_ok : fam32.walk [(11,-1),(1,1),(0,1),(9,-1),(3,0),(2,-1)] fam32_t17 = true := by decide +kernel

theorem fam32_t18_ok : fam32.walk [(11,0),(1,1),(0,1),(9,-1),(3,0),(2,-1)] fam32_t18 = true := by decide +kernel

theorem fam32_t19_ok : fam32.walk [(7,-1),(11,1),(1,1),(0,1),(9,-1),(3,0),(2,-1)] fam32_t19 = true := by decide +kernel

theorem fam32_t20_ok : fam32.walk [(7,0),(11,1),(1,1),(0,1),(9,-1),(3,0),(2,-1)] fam32_t20 = true := by decide +kernel

theorem fam32_t21_ok : fam32.walk [(7,1),(11,1),(1,1),(0,1),(9,-1),(3,0),(2,-1)] fam32_t21 = true := by decide +kernel

theorem fam32_t22_ok : fam32.walk [(9,0),(3,0),(2,-1)] fam32_t22 = true := by decide +kernel

theorem fam32_t23_ok : fam32.walk [(9,1),(3,0),(2,-1)] fam32_t23 = true := by decide +kernel

theorem fam32_t24_ok : fam32.walk [(0,-1),(3,1),(2,-1)] fam32_t24 = true := by decide +kernel

theorem fam32_t25_ok : fam32.walk [(0,0),(3,1),(2,-1)] fam32_t25 = true := by decide +kernel

end Kalai5.LemmaA
