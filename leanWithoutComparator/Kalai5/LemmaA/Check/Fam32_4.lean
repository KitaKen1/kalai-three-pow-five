import Kalai5.LemmaA.Data.Fam32

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam32_t38_ok : fam32.walk [(7,-1),(8,-1),(1,-1),(0,-1),(3,-1),(2,1)] fam32_t38 = true := by decide +kernel

theorem fam32_t39_ok : fam32.walk [(7,0),(8,-1),(1,-1),(0,-1),(3,-1),(2,1)] fam32_t39 = true := by decide +kernel

theorem fam32_t40_ok : fam32.walk [(7,1),(8,-1),(1,-1),(0,-1),(3,-1),(2,1)] fam32_t40 = true := by decide +kernel

theorem fam32_t41_ok : fam32.walk [(8,0),(1,-1),(0,-1),(3,-1),(2,1)] fam32_t41 = true := by decide +kernel

theorem fam32_t42_ok : fam32.walk [(8,1),(1,-1),(0,-1),(3,-1),(2,1)] fam32_t42 = true := by decide +kernel

theorem fam32_t43_ok : fam32.walk [(1,0),(0,-1),(3,-1),(2,1)] fam32_t43 = true := by decide +kernel

theorem fam32_t44_ok : fam32.walk [(7,-1),(1,1),(0,-1),(3,-1),(2,1)] fam32_t44 = true := by decide +kernel

theorem fam32_t45_ok : fam32.walk [(7,0),(1,1),(0,-1),(3,-1),(2,1)] fam32_t45 = true := by decide +kernel

theorem fam32_t46_ok : fam32.walk [(8,-1),(7,1),(1,1),(0,-1),(3,-1),(2,1)] fam32_t46 = true := by decide +kernel

theorem fam32_t47_ok : fam32.walk [(8,0),(7,1),(1,1),(0,-1),(3,-1),(2,1)] fam32_t47 = true := by decide +kernel

theorem fam32_t48_ok : fam32.walk [(8,1),(7,1),(1,1),(0,-1),(3,-1),(2,1)] fam32_t48 = true := by decide +kernel

theorem fam32_t49_ok : fam32.walk [(0,0),(3,-1),(2,1)] fam32_t49 = true := by decide +kernel

end Kalai5.LemmaA
