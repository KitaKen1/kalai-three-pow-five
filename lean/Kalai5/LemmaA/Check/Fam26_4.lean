import Kalai5.LemmaA.Data.Fam26

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam26_t41_ok : fam26.walk [(0,0),(19,1),(9,-1),(11,1),(4,1),(1,1),(2,-1)] fam26_t41 = true := by decide +kernel

theorem fam26_t42_ok : fam26.walk [(0,1),(19,1),(9,-1),(11,1),(4,1),(1,1),(2,-1)] fam26_t42 = true := by decide +kernel

theorem fam26_t43_ok : fam26.walk [(0,-1),(9,0),(11,1),(4,1),(1,1),(2,-1)] fam26_t43 = true := by decide +kernel

theorem fam26_t44_ok : fam26.walk [(0,0),(9,0),(11,1),(4,1),(1,1),(2,-1)] fam26_t44 = true := by decide +kernel

theorem fam26_t45_ok : fam26.walk [(0,1),(9,0),(11,1),(4,1),(1,1),(2,-1)] fam26_t45 = true := by decide +kernel

theorem fam26_t46_ok : fam26.walk [(6,-1),(9,1),(11,1),(4,1),(1,1),(2,-1)] fam26_t46 = true := by decide +kernel

theorem fam26_t47_ok : fam26.walk [(6,0),(9,1),(11,1),(4,1),(1,1),(2,-1)] fam26_t47 = true := by decide +kernel

theorem fam26_t48_ok : fam26.walk [(10,-1),(6,1),(9,1),(11,1),(4,1),(1,1),(2,-1)] fam26_t48 = true := by decide +kernel

theorem fam26_t49_ok : fam26.walk [(10,0),(6,1),(9,1),(11,1),(4,1),(1,1),(2,-1)] fam26_t49 = true := by decide +kernel

theorem fam26_t50_ok : fam26.walk [(10,1),(6,1),(9,1),(11,1),(4,1),(1,1),(2,-1)] fam26_t50 = true := by decide +kernel

theorem fam26_t51_ok : fam26.walk [(2,0)] fam26_t51 = true := by decide +kernel

theorem fam26_t52_ok : fam26.walk [(10,-1),(6,-1),(9,-1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t52 = true := by decide +kernel

end Kalai5.LemmaA
