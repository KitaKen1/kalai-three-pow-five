import Kalai5.LemmaA.Data.Fam22

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam22_f0_ok : fam22_f0.all fam22.recOK = true := by decide +kernel

theorem fam22_f1_ok : fam22_f1.all fam22.recOK = true := by decide +kernel

theorem fam22_f2_ok : fam22_f2.all fam22.recOK = true := by decide +kernel

theorem fam22_f3_ok : fam22_f3.all fam22.recOK = true := by decide +kernel

theorem fam22_f4_ok : fam22_f4.all fam22.recOK = true := by decide +kernel

theorem fam22_f5_ok : fam22_f5.all fam22.recOK = true := by decide +kernel

theorem fam22_f6_ok : fam22_f6.all fam22.recOK = true := by decide +kernel

theorem fam22_f7_ok : fam22_f7.all fam22.recOK = true := by decide +kernel

theorem fam22_t0_ok : fam22.walk [(14,-1),(8,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam22_t0 = true := by decide +kernel

theorem fam22_t1_ok : fam22.walk [(14,0),(8,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam22_t1 = true := by decide +kernel

theorem fam22_t2_ok : fam22.walk [(14,1),(8,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam22_t2 = true := by decide +kernel

theorem fam22_t3_ok : fam22.walk [(8,0),(6,-1),(0,-1),(1,-1),(2,-1)] fam22_t3 = true := by decide +kernel

end Kalai5.LemmaA
