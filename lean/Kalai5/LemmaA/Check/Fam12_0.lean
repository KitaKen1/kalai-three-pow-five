import Kalai5.LemmaA.Data.Fam12

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam12_f0_ok : fam12_f0.all fam12.recOK = true := by decide +kernel

theorem fam12_f1_ok : fam12_f1.all fam12.recOK = true := by decide +kernel

theorem fam12_f2_ok : fam12_f2.all fam12.recOK = true := by decide +kernel

theorem fam12_f3_ok : fam12_f3.all fam12.recOK = true := by decide +kernel

theorem fam12_f4_ok : fam12_f4.all fam12.recOK = true := by decide +kernel

theorem fam12_f5_ok : fam12_f5.all fam12.recOK = true := by decide +kernel

theorem fam12_f6_ok : fam12_f6.all fam12.recOK = true := by decide +kernel

theorem fam12_f7_ok : fam12_f7.all fam12.recOK = true := by decide +kernel

theorem fam12_f8_ok : fam12_f8.all fam12.recOK = true := by decide +kernel

theorem fam12_f9_ok : fam12_f9.all fam12.recOK = true := by decide +kernel

theorem fam12_t0_ok : fam12.walk [(5,-1),(8,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam12_t0 = true := by decide +kernel

theorem fam12_t1_ok : fam12.walk [(5,0),(8,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam12_t1 = true := by decide +kernel

end Kalai5.LemmaA
