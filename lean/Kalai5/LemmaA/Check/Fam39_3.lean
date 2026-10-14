import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_t28_ok : fam39.walk [(10,0),(1,-1),(0,-1),(11,1),(9,-1),(3,0),(2,-1)] fam39_t28 = true := by decide +kernel

theorem fam39_t29_ok : fam39.walk [(10,1),(1,-1),(0,-1),(11,1),(9,-1),(3,0),(2,-1)] fam39_t29 = true := by decide +kernel

theorem fam39_t30_ok : fam39.walk [(1,0),(0,-1),(11,1),(9,-1),(3,0),(2,-1)] fam39_t30 = true := by decide +kernel

theorem fam39_t31_ok : fam39.walk [(1,1),(0,-1),(11,1),(9,-1),(3,0),(2,-1)] fam39_t31 = true := by decide +kernel

theorem fam39_t32_ok : fam39.walk [(0,0),(11,1),(9,-1),(3,0),(2,-1)] fam39_t32 = true := by decide +kernel

theorem fam39_t33_ok : fam39.walk [(0,1),(11,1),(9,-1),(3,0),(2,-1)] fam39_t33 = true := by decide +kernel

theorem fam39_t34_ok : fam39.walk [(9,0),(3,0),(2,-1)] fam39_t34 = true := by decide +kernel

theorem fam39_t35_ok : fam39.walk [(9,1),(3,0),(2,-1)] fam39_t35 = true := by decide +kernel

theorem fam39_t36_ok : fam39.walk [(10,-1),(5,-1),(1,-1),(0,-1),(4,-1),(3,1),(2,-1)] fam39_t36 = true := by decide +kernel

theorem fam39_t37_ok : fam39.walk [(10,0),(5,-1),(1,-1),(0,-1),(4,-1),(3,1),(2,-1)] fam39_t37 = true := by decide +kernel

theorem fam39_t38_ok : fam39.walk [(10,1),(5,-1),(1,-1),(0,-1),(4,-1),(3,1),(2,-1)] fam39_t38 = true := by decide +kernel

theorem fam39_t39_ok : fam39.walk [(5,0),(1,-1),(0,-1),(4,-1),(3,1),(2,-1)] fam39_t39 = true := by decide +kernel

end Kalai5.LemmaA
