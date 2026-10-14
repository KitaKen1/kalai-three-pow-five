import Kalai5.LemmaA.Data.Fam0

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam0_f0_ok : fam0_f0.all fam0.recOK = true := by decide +kernel

theorem fam0_f1_ok : fam0_f1.all fam0.recOK = true := by decide +kernel

theorem fam0_f2_ok : fam0_f2.all fam0.recOK = true := by decide +kernel

theorem fam0_f3_ok : fam0_f3.all fam0.recOK = true := by decide +kernel

theorem fam0_f4_ok : fam0_f4.all fam0.recOK = true := by decide +kernel

theorem fam0_f5_ok : fam0_f5.all fam0.recOK = true := by decide +kernel

theorem fam0_f6_ok : fam0_f6.all fam0.recOK = true := by decide +kernel

theorem fam0_f7_ok : fam0_f7.all fam0.recOK = true := by decide +kernel

theorem fam0_f8_ok : fam0_f8.all fam0.recOK = true := by decide +kernel

theorem fam0_f9_ok : fam0_f9.all fam0.recOK = true := by decide +kernel

theorem fam0_t0_ok : fam0.walk [(3,-1),(1,-1),(0,-1),(2,-1)] fam0_t0 = true := by decide +kernel

theorem fam0_t1_ok : fam0.walk [(3,0),(1,-1),(0,-1),(2,-1)] fam0_t1 = true := by decide +kernel

end Kalai5.LemmaA
