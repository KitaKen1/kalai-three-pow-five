import Kalai5.LemmaA.Data.Fam38

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam38_t16_ok : fam38.walk [(8,0),(1,1),(0,0),(3,-1),(2,-1)] fam38_t16 = true := by decide +kernel

theorem fam38_t17_ok : fam38.walk [(8,1),(1,1),(0,0),(3,-1),(2,-1)] fam38_t17 = true := by decide +kernel

theorem fam38_t18_ok : fam38.walk [(1,-1),(0,1),(3,-1),(2,-1)] fam38_t18 = true := by decide +kernel

theorem fam38_t19_ok : fam38.walk [(1,0),(0,1),(3,-1),(2,-1)] fam38_t19 = true := by decide +kernel

theorem fam38_t20_ok : fam38.walk [(11,-1),(8,-1),(1,1),(0,1),(3,-1),(2,-1)] fam38_t20 = true := by decide +kernel

theorem fam38_t21_ok : fam38.walk [(11,0),(8,-1),(1,1),(0,1),(3,-1),(2,-1)] fam38_t21 = true := by decide +kernel

theorem fam38_t22_ok : fam38.walk [(11,1),(8,-1),(1,1),(0,1),(3,-1),(2,-1)] fam38_t22 = true := by decide +kernel

theorem fam38_t23_ok : fam38.walk [(8,0),(1,1),(0,1),(3,-1),(2,-1)] fam38_t23 = true := by decide +kernel

theorem fam38_t24_ok : fam38.walk [(8,1),(1,1),(0,1),(3,-1),(2,-1)] fam38_t24 = true := by decide +kernel

theorem fam38_t25_ok : fam38.walk [(11,-1),(3,0),(2,-1)] fam38_t25 = true := by decide +kernel

theorem fam38_t26_ok : fam38.walk [(11,0),(3,0),(2,-1)] fam38_t26 = true := by decide +kernel

theorem fam38_t27_ok : fam38.walk [(0,-1),(11,1),(3,0),(2,-1)] fam38_t27 = true := by decide +kernel

end Kalai5.LemmaA
