import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_t40_ok : fam39.walk [(5,1),(1,-1),(0,-1),(4,-1),(3,1),(2,-1)] fam39_t40 = true := by decide +kernel

theorem fam39_t41_ok : fam39.walk [(1,0),(0,-1),(4,-1),(3,1),(2,-1)] fam39_t41 = true := by decide +kernel

theorem fam39_t42_ok : fam39.walk [(1,1),(0,-1),(4,-1),(3,1),(2,-1)] fam39_t42 = true := by decide +kernel

theorem fam39_t43_ok : fam39.walk [(0,0),(4,-1),(3,1),(2,-1)] fam39_t43 = true := by decide +kernel

theorem fam39_t44_ok : fam39.walk [(0,1),(4,-1),(3,1),(2,-1)] fam39_t44 = true := by decide +kernel

theorem fam39_t45_ok : fam39.walk [(4,0),(3,1),(2,-1)] fam39_t45 = true := by decide +kernel

theorem fam39_t46_ok : fam39.walk [(14,-1),(4,1),(3,1),(2,-1)] fam39_t46 = true := by decide +kernel

theorem fam39_t47_ok : fam39.walk [(14,0),(4,1),(3,1),(2,-1)] fam39_t47 = true := by decide +kernel

theorem fam39_t48_ok : fam39.walk [(5,-1),(1,-1),(0,-1),(14,1),(4,1),(3,1),(2,-1)] fam39_t48 = true := by decide +kernel

theorem fam39_t49_ok : fam39.walk [(5,0),(1,-1),(0,-1),(14,1),(4,1),(3,1),(2,-1)] fam39_t49 = true := by decide +kernel

theorem fam39_t50_ok : fam39.walk [(5,1),(1,-1),(0,-1),(14,1),(4,1),(3,1),(2,-1)] fam39_t50 = true := by decide +kernel

theorem fam39_t51_ok : fam39.walk [(1,0),(0,-1),(14,1),(4,1),(3,1),(2,-1)] fam39_t51 = true := by decide +kernel

end Kalai5.LemmaA
