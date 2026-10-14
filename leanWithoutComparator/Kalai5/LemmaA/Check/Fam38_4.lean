import Kalai5.LemmaA.Data.Fam38

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam38_t40_ok : fam38.walk [(0,-1),(8,1),(11,1),(3,1),(2,-1)] fam38_t40 = true := by decide +kernel

theorem fam38_t41_ok : fam38.walk [(0,0),(8,1),(11,1),(3,1),(2,-1)] fam38_t41 = true := by decide +kernel

theorem fam38_t42_ok : fam38.walk [(10,-1),(0,1),(8,1),(11,1),(3,1),(2,-1)] fam38_t42 = true := by decide +kernel

theorem fam38_t43_ok : fam38.walk [(10,0),(0,1),(8,1),(11,1),(3,1),(2,-1)] fam38_t43 = true := by decide +kernel

theorem fam38_t44_ok : fam38.walk [(1,-1),(10,1),(0,1),(8,1),(11,1),(3,1),(2,-1)] fam38_t44 = true := by decide +kernel

theorem fam38_t45_ok : fam38.walk [(1,0),(10,1),(0,1),(8,1),(11,1),(3,1),(2,-1)] fam38_t45 = true := by decide +kernel

theorem fam38_t46_ok : fam38.walk [(1,1),(10,1),(0,1),(8,1),(11,1),(3,1),(2,-1)] fam38_t46 = true := by decide +kernel

theorem fam38_t47_ok : fam38.walk [(2,0)] fam38_t47 = true := by decide +kernel

theorem fam38_t48_ok : fam38.walk [(1,-1),(10,-1),(0,-1),(8,-1),(11,-1),(3,-1),(2,1)] fam38_t48 = true := by decide +kernel

theorem fam38_t49_ok : fam38.walk [(1,0),(10,-1),(0,-1),(8,-1),(11,-1),(3,-1),(2,1)] fam38_t49 = true := by decide +kernel

theorem fam38_t50_ok : fam38.walk [(1,1),(10,-1),(0,-1),(8,-1),(11,-1),(3,-1),(2,1)] fam38_t50 = true := by decide +kernel

theorem fam38_t51_ok : fam38.walk [(10,0),(0,-1),(8,-1),(11,-1),(3,-1),(2,1)] fam38_t51 = true := by decide +kernel

end Kalai5.LemmaA
