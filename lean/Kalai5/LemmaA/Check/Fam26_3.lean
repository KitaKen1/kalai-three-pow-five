import Kalai5.LemmaA.Data.Fam26

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam26_t29_ok : fam26.walk [(10,0),(3,-1),(0,-1),(4,-1),(1,1),(2,-1)] fam26_t29 = true := by decide +kernel

theorem fam26_t30_ok : fam26.walk [(10,1),(3,-1),(0,-1),(4,-1),(1,1),(2,-1)] fam26_t30 = true := by decide +kernel

theorem fam26_t31_ok : fam26.walk [(3,0),(0,-1),(4,-1),(1,1),(2,-1)] fam26_t31 = true := by decide +kernel

theorem fam26_t32_ok : fam26.walk [(3,1),(0,-1),(4,-1),(1,1),(2,-1)] fam26_t32 = true := by decide +kernel

theorem fam26_t33_ok : fam26.walk [(0,0),(4,-1),(1,1),(2,-1)] fam26_t33 = true := by decide +kernel

theorem fam26_t34_ok : fam26.walk [(0,1),(4,-1),(1,1),(2,-1)] fam26_t34 = true := by decide +kernel

theorem fam26_t35_ok : fam26.walk [(4,0),(1,1),(2,-1)] fam26_t35 = true := by decide +kernel

theorem fam26_t36_ok : fam26.walk [(11,-1),(4,1),(1,1),(2,-1)] fam26_t36 = true := by decide +kernel

theorem fam26_t37_ok : fam26.walk [(11,0),(4,1),(1,1),(2,-1)] fam26_t37 = true := by decide +kernel

theorem fam26_t38_ok : fam26.walk [(19,-1),(9,-1),(11,1),(4,1),(1,1),(2,-1)] fam26_t38 = true := by decide +kernel

theorem fam26_t39_ok : fam26.walk [(19,0),(9,-1),(11,1),(4,1),(1,1),(2,-1)] fam26_t39 = true := by decide +kernel

theorem fam26_t40_ok : fam26.walk [(0,-1),(19,1),(9,-1),(11,1),(4,1),(1,1),(2,-1)] fam26_t40 = true := by decide +kernel

end Kalai5.LemmaA
