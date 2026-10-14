import Kalai5.LemmaA.Data.Fam32

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam32_t26_ok : fam32.walk [(8,-1),(7,-1),(1,-1),(0,1),(3,1),(2,-1)] fam32_t26 = true := by decide +kernel

theorem fam32_t27_ok : fam32.walk [(8,0),(7,-1),(1,-1),(0,1),(3,1),(2,-1)] fam32_t27 = true := by decide +kernel

theorem fam32_t28_ok : fam32.walk [(8,1),(7,-1),(1,-1),(0,1),(3,1),(2,-1)] fam32_t28 = true := by decide +kernel

theorem fam32_t29_ok : fam32.walk [(7,0),(1,-1),(0,1),(3,1),(2,-1)] fam32_t29 = true := by decide +kernel

theorem fam32_t30_ok : fam32.walk [(7,1),(1,-1),(0,1),(3,1),(2,-1)] fam32_t30 = true := by decide +kernel

theorem fam32_t31_ok : fam32.walk [(1,0),(0,1),(3,1),(2,-1)] fam32_t31 = true := by decide +kernel

theorem fam32_t32_ok : fam32.walk [(8,-1),(1,1),(0,1),(3,1),(2,-1)] fam32_t32 = true := by decide +kernel

theorem fam32_t33_ok : fam32.walk [(8,0),(1,1),(0,1),(3,1),(2,-1)] fam32_t33 = true := by decide +kernel

theorem fam32_t34_ok : fam32.walk [(7,-1),(8,1),(1,1),(0,1),(3,1),(2,-1)] fam32_t34 = true := by decide +kernel

theorem fam32_t35_ok : fam32.walk [(7,0),(8,1),(1,1),(0,1),(3,1),(2,-1)] fam32_t35 = true := by decide +kernel

theorem fam32_t36_ok : fam32.walk [(7,1),(8,1),(1,1),(0,1),(3,1),(2,-1)] fam32_t36 = true := by decide +kernel

theorem fam32_t37_ok : fam32.walk [(2,0)] fam32_t37 = true := by decide +kernel

end Kalai5.LemmaA
