import Kalai5.LemmaA.Data.Fam15

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam15_f0_ok : fam15_f0.all fam15.recOK = true := by decide +kernel

theorem fam15_f1_ok : fam15_f1.all fam15.recOK = true := by decide +kernel

theorem fam15_f2_ok : fam15_f2.all fam15.recOK = true := by decide +kernel

theorem fam15_f3_ok : fam15_f3.all fam15.recOK = true := by decide +kernel

theorem fam15_f4_ok : fam15_f4.all fam15.recOK = true := by decide +kernel

theorem fam15_f5_ok : fam15_f5.all fam15.recOK = true := by decide +kernel

theorem fam15_f6_ok : fam15_f6.all fam15.recOK = true := by decide +kernel

theorem fam15_f7_ok : fam15_f7.all fam15.recOK = true := by decide +kernel

theorem fam15_f8_ok : fam15_f8.all fam15.recOK = true := by decide +kernel

theorem fam15_t0_ok : fam15.walk [(0,-1),(8,-1),(1,-1),(2,-1)] fam15_t0 = true := by decide +kernel

theorem fam15_t1_ok : fam15.walk [(0,0),(8,-1),(1,-1),(2,-1)] fam15_t1 = true := by decide +kernel

theorem fam15_t2_ok : fam15.walk [(0,1),(8,-1),(1,-1),(2,-1)] fam15_t2 = true := by decide +kernel

end Kalai5.LemmaA
