import Kalai5.LemmaA.Data.Fam44

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam44_t15_ok : fam44.walk [(0,1),(1,0),(3,-1)] fam44_t15 = true := by decide +kernel

theorem fam44_t16_ok : fam44.walk [(2,-1),(5,-1),(1,1),(3,-1)] fam44_t16 = true := by decide +kernel

theorem fam44_t17_ok : fam44.walk [(2,0),(5,-1),(1,1),(3,-1)] fam44_t17 = true := by decide +kernel

theorem fam44_t18_ok : fam44.walk [(0,-1),(13,-1),(4,-1),(2,1),(5,-1),(1,1),(3,-1)] fam44_t18 = true := by decide +kernel

theorem fam44_t19_ok : fam44.walk [(0,0),(13,-1),(4,-1),(2,1),(5,-1),(1,1),(3,-1)] fam44_t19 = true := by decide +kernel

theorem fam44_t20_ok : fam44.walk [(0,1),(13,-1),(4,-1),(2,1),(5,-1),(1,1),(3,-1)] fam44_t20 = true := by decide +kernel

theorem fam44_t21_ok : fam44.walk [(13,0),(4,-1),(2,1),(5,-1),(1,1),(3,-1)] fam44_t21 = true := by decide +kernel

theorem fam44_t22_ok : fam44.walk [(13,1),(4,-1),(2,1),(5,-1),(1,1),(3,-1)] fam44_t22 = true := by decide +kernel

theorem fam44_t23_ok : fam44.walk [(4,0),(2,1),(5,-1),(1,1),(3,-1)] fam44_t23 = true := by decide +kernel

theorem fam44_t24_ok : fam44.walk [(4,1),(2,1),(5,-1),(1,1),(3,-1)] fam44_t24 = true := by decide +kernel

theorem fam44_t25_ok : fam44.walk [(5,0),(1,1),(3,-1)] fam44_t25 = true := by decide +kernel

theorem fam44_t26_ok : fam44.walk [(2,-1),(13,-1),(4,-1),(5,1),(1,1),(3,-1)] fam44_t26 = true := by decide +kernel

end Kalai5.LemmaA
