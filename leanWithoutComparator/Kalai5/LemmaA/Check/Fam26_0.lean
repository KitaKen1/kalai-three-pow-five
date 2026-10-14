import Kalai5.LemmaA.Data.Fam26

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam26_f0_ok : fam26_f0.all fam26.recOK = true := by decide +kernel

theorem fam26_f1_ok : fam26_f1.all fam26.recOK = true := by decide +kernel

theorem fam26_f2_ok : fam26_f2.all fam26.recOK = true := by decide +kernel

theorem fam26_f3_ok : fam26_f3.all fam26.recOK = true := by decide +kernel

theorem fam26_f4_ok : fam26_f4.all fam26.recOK = true := by decide +kernel

theorem fam26_f5_ok : fam26_f5.all fam26.recOK = true := by decide +kernel

theorem fam26_f6_ok : fam26_f6.all fam26.recOK = true := by decide +kernel

theorem fam26_t0_ok : fam26.walk [(3,-1),(8,-1),(5,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t0 = true := by decide +kernel

theorem fam26_t1_ok : fam26.walk [(3,0),(8,-1),(5,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t1 = true := by decide +kernel

theorem fam26_t2_ok : fam26.walk [(3,1),(8,-1),(5,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t2 = true := by decide +kernel

theorem fam26_t3_ok : fam26.walk [(8,0),(5,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t3 = true := by decide +kernel

theorem fam26_t4_ok : fam26.walk [(8,1),(5,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_t4 = true := by decide +kernel

end Kalai5.LemmaA
