import Kalai5.LemmaA.Data.Fam44

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam44_f0_ok : fam44_f0.all fam44.recOK = true := by decide +kernel

theorem fam44_f1_ok : fam44_f1.all fam44.recOK = true := by decide +kernel

theorem fam44_f2_ok : fam44_f2.all fam44.recOK = true := by decide +kernel

theorem fam44_f3_ok : fam44_f3.all fam44.recOK = true := by decide +kernel

theorem fam44_f4_ok : fam44_f4.all fam44.recOK = true := by decide +kernel

theorem fam44_f5_ok : fam44_f5.all fam44.recOK = true := by decide +kernel

theorem fam44_f6_ok : fam44_f6.all fam44.recOK = true := by decide +kernel

theorem fam44_f7_ok : fam44_f7.all fam44.recOK = true := by decide +kernel

theorem fam44_f8_ok : fam44_f8.all fam44.recOK = true := by decide +kernel

theorem fam44_t0_ok : fam44.walk [(5,-1),(9,-1),(2,-1),(0,-1),(1,-1),(3,-1)] fam44_t0 = true := by decide +kernel

theorem fam44_t1_ok : fam44.walk [(5,0),(9,-1),(2,-1),(0,-1),(1,-1),(3,-1)] fam44_t1 = true := by decide +kernel

theorem fam44_t2_ok : fam44.walk [(4,-1),(5,1),(9,-1),(2,-1),(0,-1),(1,-1),(3,-1)] fam44_t2 = true := by decide +kernel

end Kalai5.LemmaA
