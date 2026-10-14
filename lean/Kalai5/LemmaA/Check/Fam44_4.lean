import Kalai5.LemmaA.Data.Fam44

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam44_t39_ok : fam44.walk [(13,1),(7,1),(4,0),(5,1),(1,1),(3,-1)] fam44_t39 = true := by decide +kernel

theorem fam44_t40_ok : fam44.walk [(7,-1),(4,1),(5,1),(1,1),(3,-1)] fam44_t40 = true := by decide +kernel

theorem fam44_t41_ok : fam44.walk [(7,0),(4,1),(5,1),(1,1),(3,-1)] fam44_t41 = true := by decide +kernel

theorem fam44_t42_ok : fam44.walk [(0,-1),(7,1),(4,1),(5,1),(1,1),(3,-1)] fam44_t42 = true := by decide +kernel

theorem fam44_t43_ok : fam44.walk [(0,0),(7,1),(4,1),(5,1),(1,1),(3,-1)] fam44_t43 = true := by decide +kernel

theorem fam44_t44_ok : fam44.walk [(2,-1),(0,1),(7,1),(4,1),(5,1),(1,1),(3,-1)] fam44_t44 = true := by decide +kernel

theorem fam44_t45_ok : fam44.walk [(2,0),(0,1),(7,1),(4,1),(5,1),(1,1),(3,-1)] fam44_t45 = true := by decide +kernel

theorem fam44_t46_ok : fam44.walk [(2,1),(0,1),(7,1),(4,1),(5,1),(1,1),(3,-1)] fam44_t46 = true := by decide +kernel

theorem fam44_t47_ok : fam44.walk [(5,-1),(0,-1),(1,-1),(3,0)] fam44_t47 = true := by decide +kernel

theorem fam44_t48_ok : fam44.walk [(5,0),(0,-1),(1,-1),(3,0)] fam44_t48 = true := by decide +kernel

theorem fam44_t49_ok : fam44.walk [(5,1),(0,-1),(1,-1),(3,0)] fam44_t49 = true := by decide +kernel

theorem fam44_t50_ok : fam44.walk [(0,0),(1,-1),(3,0)] fam44_t50 = true := by decide +kernel

end Kalai5.LemmaA
