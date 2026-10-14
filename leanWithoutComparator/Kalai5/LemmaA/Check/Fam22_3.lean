import Kalai5.LemmaA.Data.Fam22

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam22_t28_ok : fam22.walk [(6,1),(0,-1),(8,-1),(1,1),(2,-1)] fam22_t28 = true := by decide +kernel

theorem fam22_t29_ok : fam22.walk [(0,0),(8,-1),(1,1),(2,-1)] fam22_t29 = true := by decide +kernel

theorem fam22_t30_ok : fam22.walk [(0,1),(8,-1),(1,1),(2,-1)] fam22_t30 = true := by decide +kernel

theorem fam22_t31_ok : fam22.walk [(14,-1),(6,-1),(0,-1),(8,0),(1,1),(2,-1)] fam22_t31 = true := by decide +kernel

theorem fam22_t32_ok : fam22.walk [(14,0),(6,-1),(0,-1),(8,0),(1,1),(2,-1)] fam22_t32 = true := by decide +kernel

theorem fam22_t33_ok : fam22.walk [(4,-1),(20,-1),(14,1),(6,-1),(0,-1),(8,0),(1,1),(2,-1)] fam22_t33 = true := by decide +kernel

theorem fam22_t34_ok : fam22.walk [(4,0),(20,-1),(14,1),(6,-1),(0,-1),(8,0),(1,1),(2,-1)] fam22_t34 = true := by decide +kernel

theorem fam22_t35_ok : fam22.walk [(4,1),(20,-1),(14,1),(6,-1),(0,-1),(8,0),(1,1),(2,-1)] fam22_t35 = true := by decide +kernel

theorem fam22_t36_ok : fam22.walk [(20,0),(14,1),(6,-1),(0,-1),(8,0),(1,1),(2,-1)] fam22_t36 = true := by decide +kernel

theorem fam22_t37_ok : fam22.walk [(20,1),(14,1),(6,-1),(0,-1),(8,0),(1,1),(2,-1)] fam22_t37 = true := by decide +kernel

theorem fam22_t38_ok : fam22.walk [(6,0),(0,-1),(8,0),(1,1),(2,-1)] fam22_t38 = true := by decide +kernel

theorem fam22_t39_ok : fam22.walk [(6,1),(0,-1),(8,0),(1,1),(2,-1)] fam22_t39 = true := by decide +kernel

end Kalai5.LemmaA
