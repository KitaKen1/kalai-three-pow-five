import Kalai5.LemmaA.Data.Fam32

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam32_f0_ok : fam32_f0.all fam32.recOK = true := by decide +kernel

theorem fam32_f1_ok : fam32_f1.all fam32.recOK = true := by decide +kernel

theorem fam32_f2_ok : fam32_f2.all fam32.recOK = true := by decide +kernel

theorem fam32_f3_ok : fam32_f3.all fam32.recOK = true := by decide +kernel

theorem fam32_f4_ok : fam32_f4.all fam32.recOK = true := by decide +kernel

theorem fam32_f5_ok : fam32_f5.all fam32.recOK = true := by decide +kernel

theorem fam32_f6_ok : fam32_f6.all fam32.recOK = true := by decide +kernel

theorem fam32_f7_ok : fam32_f7.all fam32.recOK = true := by decide +kernel

theorem fam32_f8_ok : fam32_f8.all fam32.recOK = true := by decide +kernel

theorem fam32_f9_ok : fam32_f9.all fam32.recOK = true := by decide +kernel

theorem fam32_t0_ok : fam32.walk [(1,-1),(3,-1),(2,-1)] fam32_t0 = true := by decide +kernel

theorem fam32_t1_ok : fam32.walk [(1,0),(3,-1),(2,-1)] fam32_t1 = true := by decide +kernel

end Kalai5.LemmaA
