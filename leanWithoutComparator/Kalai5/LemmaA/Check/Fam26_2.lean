import Kalai5.LemmaA.Data.Fam26

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam26_t17_ok : fam26.walk [(3,0),(0,1),(1,-1),(2,-1)] fam26_t17 = true := by decide +kernel

theorem fam26_t18_ok : fam26.walk [(4,-1),(3,1),(0,1),(1,-1),(2,-1)] fam26_t18 = true := by decide +kernel

theorem fam26_t19_ok : fam26.walk [(4,0),(3,1),(0,1),(1,-1),(2,-1)] fam26_t19 = true := by decide +kernel

theorem fam26_t20_ok : fam26.walk [(10,-1),(4,1),(3,1),(0,1),(1,-1),(2,-1)] fam26_t20 = true := by decide +kernel

theorem fam26_t21_ok : fam26.walk [(10,0),(4,1),(3,1),(0,1),(1,-1),(2,-1)] fam26_t21 = true := by decide +kernel

theorem fam26_t22_ok : fam26.walk [(8,-1),(10,1),(4,1),(3,1),(0,1),(1,-1),(2,-1)] fam26_t22 = true := by decide +kernel

theorem fam26_t23_ok : fam26.walk [(8,0),(10,1),(4,1),(3,1),(0,1),(1,-1),(2,-1)] fam26_t23 = true := by decide +kernel

theorem fam26_t24_ok : fam26.walk [(8,1),(10,1),(4,1),(3,1),(0,1),(1,-1),(2,-1)] fam26_t24 = true := by decide +kernel

theorem fam26_t25_ok : fam26.walk [(1,0),(2,-1)] fam26_t25 = true := by decide +kernel

theorem fam26_t26_ok : fam26.walk [(6,-1),(10,-1),(3,-1),(0,-1),(4,-1),(1,1),(2,-1)] fam26_t26 = true := by decide +kernel

theorem fam26_t27_ok : fam26.walk [(6,0),(10,-1),(3,-1),(0,-1),(4,-1),(1,1),(2,-1)] fam26_t27 = true := by decide +kernel

theorem fam26_t28_ok : fam26.walk [(6,1),(10,-1),(3,-1),(0,-1),(4,-1),(1,1),(2,-1)] fam26_t28 = true := by decide +kernel

end Kalai5.LemmaA
