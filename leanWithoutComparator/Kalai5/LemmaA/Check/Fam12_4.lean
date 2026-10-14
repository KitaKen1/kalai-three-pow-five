import Kalai5.LemmaA.Data.Fam12

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam12_t38_ok : fam12.walk [(8,1),(6,-1),(1,-1),(2,1)] fam12_t38 = true := by decide +kernel

theorem fam12_t39_ok : fam12.walk [(6,0),(1,-1),(2,1)] fam12_t39 = true := by decide +kernel

theorem fam12_t40_ok : fam12.walk [(0,-1),(6,1),(1,-1),(2,1)] fam12_t40 = true := by decide +kernel

theorem fam12_t41_ok : fam12.walk [(0,0),(6,1),(1,-1),(2,1)] fam12_t41 = true := by decide +kernel

theorem fam12_t42_ok : fam12.walk [(4,-1),(0,1),(6,1),(1,-1),(2,1)] fam12_t42 = true := by decide +kernel

theorem fam12_t43_ok : fam12.walk [(4,0),(0,1),(6,1),(1,-1),(2,1)] fam12_t43 = true := by decide +kernel

theorem fam12_t44_ok : fam12.walk [(9,-1),(4,1),(0,1),(6,1),(1,-1),(2,1)] fam12_t44 = true := by decide +kernel

theorem fam12_t45_ok : fam12.walk [(9,0),(4,1),(0,1),(6,1),(1,-1),(2,1)] fam12_t45 = true := by decide +kernel

theorem fam12_t46_ok : fam12.walk [(9,1),(4,1),(0,1),(6,1),(1,-1),(2,1)] fam12_t46 = true := by decide +kernel

theorem fam12_t47_ok : fam12.walk [(1,0),(2,1)] fam12_t47 = true := by decide +kernel

theorem fam12_t48_ok : fam12.walk [(5,-1),(8,-1),(4,-1),(0,-1),(1,1),(2,1)] fam12_t48 = true := by decide +kernel

theorem fam12_t49_ok : fam12.walk [(5,0),(8,-1),(4,-1),(0,-1),(1,1),(2,1)] fam12_t49 = true := by decide +kernel

end Kalai5.LemmaA
