import Kalai5.LemmaA.Data.Fam38

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam38_f0_ok : fam38_f0.all fam38.recOK = true := by decide +kernel

theorem fam38_f1_ok : fam38_f1.all fam38.recOK = true := by decide +kernel

theorem fam38_f2_ok : fam38_f2.all fam38.recOK = true := by decide +kernel

theorem fam38_f3_ok : fam38_f3.all fam38.recOK = true := by decide +kernel

theorem fam38_f4_ok : fam38_f4.all fam38.recOK = true := by decide +kernel

theorem fam38_f5_ok : fam38_f5.all fam38.recOK = true := by decide +kernel

theorem fam38_f6_ok : fam38_f6.all fam38.recOK = true := by decide +kernel

theorem fam38_f7_ok : fam38_f7.all fam38.recOK = true := by decide +kernel

theorem fam38_t0_ok : fam38.walk [(1,-1),(11,-1),(10,-1),(8,-1),(0,-1),(3,-1),(2,-1)] fam38_t0 = true := by decide +kernel

theorem fam38_t1_ok : fam38.walk [(1,0),(11,-1),(10,-1),(8,-1),(0,-1),(3,-1),(2,-1)] fam38_t1 = true := by decide +kernel

theorem fam38_t2_ok : fam38.walk [(1,1),(11,-1),(10,-1),(8,-1),(0,-1),(3,-1),(2,-1)] fam38_t2 = true := by decide +kernel

theorem fam38_t3_ok : fam38.walk [(11,0),(10,-1),(8,-1),(0,-1),(3,-1),(2,-1)] fam38_t3 = true := by decide +kernel

end Kalai5.LemmaA
