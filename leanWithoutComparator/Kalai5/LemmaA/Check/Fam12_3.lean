import Kalai5.LemmaA.Data.Fam12

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam12_t26_ok : fam12.walk [(4,-1),(8,1),(6,1),(1,1),(2,-1)] fam12_t26 = true := by decide +kernel

theorem fam12_t27_ok : fam12.walk [(4,0),(8,1),(6,1),(1,1),(2,-1)] fam12_t27 = true := by decide +kernel

theorem fam12_t28_ok : fam12.walk [(9,-1),(4,1),(8,1),(6,1),(1,1),(2,-1)] fam12_t28 = true := by decide +kernel

theorem fam12_t29_ok : fam12.walk [(9,0),(4,1),(8,1),(6,1),(1,1),(2,-1)] fam12_t29 = true := by decide +kernel

theorem fam12_t30_ok : fam12.walk [(9,1),(4,1),(8,1),(6,1),(1,1),(2,-1)] fam12_t30 = true := by decide +kernel

theorem fam12_t31_ok : fam12.walk [(2,0)] fam12_t31 = true := by decide +kernel

theorem fam12_t32_ok : fam12.walk [(9,-1),(4,-1),(8,-1),(6,-1),(1,-1),(2,1)] fam12_t32 = true := by decide +kernel

theorem fam12_t33_ok : fam12.walk [(9,0),(4,-1),(8,-1),(6,-1),(1,-1),(2,1)] fam12_t33 = true := by decide +kernel

theorem fam12_t34_ok : fam12.walk [(9,1),(4,-1),(8,-1),(6,-1),(1,-1),(2,1)] fam12_t34 = true := by decide +kernel

theorem fam12_t35_ok : fam12.walk [(4,0),(8,-1),(6,-1),(1,-1),(2,1)] fam12_t35 = true := by decide +kernel

theorem fam12_t36_ok : fam12.walk [(4,1),(8,-1),(6,-1),(1,-1),(2,1)] fam12_t36 = true := by decide +kernel

theorem fam12_t37_ok : fam12.walk [(8,0),(6,-1),(1,-1),(2,1)] fam12_t37 = true := by decide +kernel

end Kalai5.LemmaA
