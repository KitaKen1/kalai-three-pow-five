import Kalai5.LemmaA.Data.Fam26

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam26_t53_ok : fam26.walk [(10,0),(6,-1),(9,-1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t53 = true := by decide +kernel

theorem fam26_t54_ok : fam26.walk [(10,1),(6,-1),(9,-1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t54 = true := by decide +kernel

theorem fam26_t55_ok : fam26.walk [(6,0),(9,-1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t55 = true := by decide +kernel

theorem fam26_t56_ok : fam26.walk [(6,1),(9,-1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t56 = true := by decide +kernel

theorem fam26_t57_ok : fam26.walk [(0,-1),(9,0),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t57 = true := by decide +kernel

theorem fam26_t58_ok : fam26.walk [(0,0),(9,0),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t58 = true := by decide +kernel

theorem fam26_t59_ok : fam26.walk [(0,1),(9,0),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t59 = true := by decide +kernel

theorem fam26_t60_ok : fam26.walk [(0,-1),(19,-1),(9,1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t60 = true := by decide +kernel

theorem fam26_t61_ok : fam26.walk [(0,0),(19,-1),(9,1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t61 = true := by decide +kernel

theorem fam26_t62_ok : fam26.walk [(0,1),(19,-1),(9,1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t62 = true := by decide +kernel

theorem fam26_t63_ok : fam26.walk [(19,0),(9,1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t63 = true := by decide +kernel

theorem fam26_t64_ok : fam26.walk [(19,1),(9,1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_t64 = true := by decide +kernel

end Kalai5.LemmaA
