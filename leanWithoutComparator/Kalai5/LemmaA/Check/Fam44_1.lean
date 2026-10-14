import Kalai5.LemmaA.Data.Fam44

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam44_t3_ok : fam44.walk [(4,0),(5,1),(9,-1),(2,-1),(0,-1),(1,-1),(3,-1)] fam44_t3 = true := by decide +kernel

theorem fam44_t4_ok : fam44.walk [(4,1),(5,1),(9,-1),(2,-1),(0,-1),(1,-1),(3,-1)] fam44_t4 = true := by decide +kernel

theorem fam44_t5_ok : fam44.walk [(9,0),(2,-1),(0,-1),(1,-1),(3,-1)] fam44_t5 = true := by decide +kernel

theorem fam44_t6_ok : fam44.walk [(9,1),(2,-1),(0,-1),(1,-1),(3,-1)] fam44_t6 = true := by decide +kernel

theorem fam44_t7_ok : fam44.walk [(2,0),(0,-1),(1,-1),(3,-1)] fam44_t7 = true := by decide +kernel

theorem fam44_t8_ok : fam44.walk [(2,1),(0,-1),(1,-1),(3,-1)] fam44_t8 = true := by decide +kernel

theorem fam44_t9_ok : fam44.walk [(0,0),(1,-1),(3,-1)] fam44_t9 = true := by decide +kernel

theorem fam44_t10_ok : fam44.walk [(0,1),(1,-1),(3,-1)] fam44_t10 = true := by decide +kernel

theorem fam44_t11_ok : fam44.walk [(5,-1),(0,-1),(1,0),(3,-1)] fam44_t11 = true := by decide +kernel

theorem fam44_t12_ok : fam44.walk [(5,0),(0,-1),(1,0),(3,-1)] fam44_t12 = true := by decide +kernel

theorem fam44_t13_ok : fam44.walk [(5,1),(0,-1),(1,0),(3,-1)] fam44_t13 = true := by decide +kernel

theorem fam44_t14_ok : fam44.walk [(0,0),(1,0),(3,-1)] fam44_t14 = true := by decide +kernel

end Kalai5.LemmaA
