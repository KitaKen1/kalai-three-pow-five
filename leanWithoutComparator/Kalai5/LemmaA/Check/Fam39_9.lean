import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_t100_ok : fam39.walk [(1,1),(0,-1),(5,-1),(4,-1),(3,1),(2,1)] fam39_t100 = true := by decide +kernel

theorem fam39_t101_ok : fam39.walk [(0,0),(5,-1),(4,-1),(3,1),(2,1)] fam39_t101 = true := by decide +kernel

theorem fam39_t102_ok : fam39.walk [(10,-1),(0,1),(5,-1),(4,-1),(3,1),(2,1)] fam39_t102 = true := by decide +kernel

theorem fam39_t103_ok : fam39.walk [(10,0),(0,1),(5,-1),(4,-1),(3,1),(2,1)] fam39_t103 = true := by decide +kernel

theorem fam39_t104_ok : fam39.walk [(1,-1),(10,1),(0,1),(5,-1),(4,-1),(3,1),(2,1)] fam39_t104 = true := by decide +kernel

theorem fam39_t105_ok : fam39.walk [(1,0),(10,1),(0,1),(5,-1),(4,-1),(3,1),(2,1)] fam39_t105 = true := by decide +kernel

theorem fam39_t106_ok : fam39.walk [(1,1),(10,1),(0,1),(5,-1),(4,-1),(3,1),(2,1)] fam39_t106 = true := by decide +kernel

theorem fam39_t107_ok : fam39.walk [(5,0),(4,-1),(3,1),(2,1)] fam39_t107 = true := by decide +kernel

theorem fam39_t108_ok : fam39.walk [(5,1),(4,-1),(3,1),(2,1)] fam39_t108 = true := by decide +kernel

theorem fam39_t109_ok : fam39.walk [(4,0),(3,1),(2,1)] fam39_t109 = true := by decide +kernel

theorem fam39_t110_ok : fam39.walk [(0,-1),(4,1),(3,1),(2,1)] fam39_t110 = true := by decide +kernel

theorem fam39_t111_ok : fam39.walk [(0,0),(4,1),(3,1),(2,1)] fam39_t111 = true := by decide +kernel

end Kalai5.LemmaA
