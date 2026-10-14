import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_f0_ok : fam39_f0.all fam39.recOK = true := by decide +kernel

theorem fam39_f1_ok : fam39_f1.all fam39.recOK = true := by decide +kernel

theorem fam39_f2_ok : fam39_f2.all fam39.recOK = true := by decide +kernel

theorem fam39_f3_ok : fam39_f3.all fam39.recOK = true := by decide +kernel

theorem fam39_f4_ok : fam39_f4.all fam39.recOK = true := by decide +kernel

theorem fam39_f5_ok : fam39_f5.all fam39.recOK = true := by decide +kernel

theorem fam39_f6_ok : fam39_f6.all fam39.recOK = true := by decide +kernel

theorem fam39_f7_ok : fam39_f7.all fam39.recOK = true := by decide +kernel

theorem fam39_t0_ok : fam39.walk [(1,-1),(14,-1),(10,-1),(0,-1),(4,-1),(3,-1),(2,-1)] fam39_t0 = true := by decide +kernel

theorem fam39_t1_ok : fam39.walk [(1,0),(14,-1),(10,-1),(0,-1),(4,-1),(3,-1),(2,-1)] fam39_t1 = true := by decide +kernel

theorem fam39_t2_ok : fam39.walk [(1,1),(14,-1),(10,-1),(0,-1),(4,-1),(3,-1),(2,-1)] fam39_t2 = true := by decide +kernel

theorem fam39_t3_ok : fam39.walk [(14,0),(10,-1),(0,-1),(4,-1),(3,-1),(2,-1)] fam39_t3 = true := by decide +kernel

end Kalai5.LemmaA
