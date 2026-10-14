import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_t16_ok : fam39.walk [(10,1),(0,-1),(5,1),(4,1),(3,-1),(2,-1)] fam39_t16 = true := by decide +kernel

theorem fam39_t17_ok : fam39.walk [(0,0),(5,1),(4,1),(3,-1),(2,-1)] fam39_t17 = true := by decide +kernel

theorem fam39_t18_ok : fam39.walk [(1,-1),(0,1),(5,1),(4,1),(3,-1),(2,-1)] fam39_t18 = true := by decide +kernel

theorem fam39_t19_ok : fam39.walk [(1,0),(0,1),(5,1),(4,1),(3,-1),(2,-1)] fam39_t19 = true := by decide +kernel

theorem fam39_t20_ok : fam39.walk [(14,-1),(1,1),(0,1),(5,1),(4,1),(3,-1),(2,-1)] fam39_t20 = true := by decide +kernel

theorem fam39_t21_ok : fam39.walk [(14,0),(1,1),(0,1),(5,1),(4,1),(3,-1),(2,-1)] fam39_t21 = true := by decide +kernel

theorem fam39_t22_ok : fam39.walk [(14,1),(1,1),(0,1),(5,1),(4,1),(3,-1),(2,-1)] fam39_t22 = true := by decide +kernel

theorem fam39_t23_ok : fam39.walk [(11,-1),(9,-1),(3,0),(2,-1)] fam39_t23 = true := by decide +kernel

theorem fam39_t24_ok : fam39.walk [(11,0),(9,-1),(3,0),(2,-1)] fam39_t24 = true := by decide +kernel

theorem fam39_t25_ok : fam39.walk [(4,-1),(10,-1),(1,-1),(0,-1),(11,1),(9,-1),(3,0),(2,-1)] fam39_t25 = true := by decide +kernel

theorem fam39_t26_ok : fam39.walk [(4,0),(10,-1),(1,-1),(0,-1),(11,1),(9,-1),(3,0),(2,-1)] fam39_t26 = true := by decide +kernel

theorem fam39_t27_ok : fam39.walk [(4,1),(10,-1),(1,-1),(0,-1),(11,1),(9,-1),(3,0),(2,-1)] fam39_t27 = true := by decide +kernel

end Kalai5.LemmaA
