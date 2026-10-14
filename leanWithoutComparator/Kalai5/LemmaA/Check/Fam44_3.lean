import Kalai5.LemmaA.Data.Fam44

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam44_t27_ok : fam44.walk [(2,0),(13,-1),(4,-1),(5,1),(1,1),(3,-1)] fam44_t27 = true := by decide +kernel

theorem fam44_t28_ok : fam44.walk [(0,-1),(2,1),(13,-1),(4,-1),(5,1),(1,1),(3,-1)] fam44_t28 = true := by decide +kernel

theorem fam44_t29_ok : fam44.walk [(0,0),(2,1),(13,-1),(4,-1),(5,1),(1,1),(3,-1)] fam44_t29 = true := by decide +kernel

theorem fam44_t30_ok : fam44.walk [(0,1),(2,1),(13,-1),(4,-1),(5,1),(1,1),(3,-1)] fam44_t30 = true := by decide +kernel

theorem fam44_t31_ok : fam44.walk [(13,0),(4,-1),(5,1),(1,1),(3,-1)] fam44_t31 = true := by decide +kernel

theorem fam44_t32_ok : fam44.walk [(13,1),(4,-1),(5,1),(1,1),(3,-1)] fam44_t32 = true := by decide +kernel

theorem fam44_t33_ok : fam44.walk [(7,-1),(4,0),(5,1),(1,1),(3,-1)] fam44_t33 = true := by decide +kernel

theorem fam44_t34_ok : fam44.walk [(7,0),(4,0),(5,1),(1,1),(3,-1)] fam44_t34 = true := by decide +kernel

theorem fam44_t35_ok : fam44.walk [(0,-1),(13,-1),(7,1),(4,0),(5,1),(1,1),(3,-1)] fam44_t35 = true := by decide +kernel

theorem fam44_t36_ok : fam44.walk [(0,0),(13,-1),(7,1),(4,0),(5,1),(1,1),(3,-1)] fam44_t36 = true := by decide +kernel

theorem fam44_t37_ok : fam44.walk [(0,1),(13,-1),(7,1),(4,0),(5,1),(1,1),(3,-1)] fam44_t37 = true := by decide +kernel

theorem fam44_t38_ok : fam44.walk [(13,0),(7,1),(4,0),(5,1),(1,1),(3,-1)] fam44_t38 = true := by decide +kernel

end Kalai5.LemmaA
