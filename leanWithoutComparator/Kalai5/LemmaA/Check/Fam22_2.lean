import Kalai5.LemmaA.Data.Fam22

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam22_t16_ok : fam22.walk [(6,0),(4,1),(0,0),(1,-1),(2,-1)] fam22_t16 = true := by decide +kernel

theorem fam22_t17_ok : fam22.walk [(6,1),(4,1),(0,0),(1,-1),(2,-1)] fam22_t17 = true := by decide +kernel

theorem fam22_t18_ok : fam22.walk [(4,-1),(0,1),(1,-1),(2,-1)] fam22_t18 = true := by decide +kernel

theorem fam22_t19_ok : fam22.walk [(4,0),(0,1),(1,-1),(2,-1)] fam22_t19 = true := by decide +kernel

theorem fam22_t20_ok : fam22.walk [(5,-1),(4,1),(0,1),(1,-1),(2,-1)] fam22_t20 = true := by decide +kernel

theorem fam22_t21_ok : fam22.walk [(5,0),(4,1),(0,1),(1,-1),(2,-1)] fam22_t21 = true := by decide +kernel

theorem fam22_t22_ok : fam22.walk [(5,1),(4,1),(0,1),(1,-1),(2,-1)] fam22_t22 = true := by decide +kernel

theorem fam22_t23_ok : fam22.walk [(1,0),(2,-1)] fam22_t23 = true := by decide +kernel

theorem fam22_t24_ok : fam22.walk [(4,-1),(6,-1),(0,-1),(8,-1),(1,1),(2,-1)] fam22_t24 = true := by decide +kernel

theorem fam22_t25_ok : fam22.walk [(4,0),(6,-1),(0,-1),(8,-1),(1,1),(2,-1)] fam22_t25 = true := by decide +kernel

theorem fam22_t26_ok : fam22.walk [(4,1),(6,-1),(0,-1),(8,-1),(1,1),(2,-1)] fam22_t26 = true := by decide +kernel

theorem fam22_t27_ok : fam22.walk [(6,0),(0,-1),(8,-1),(1,1),(2,-1)] fam22_t27 = true := by decide +kernel

end Kalai5.LemmaA
