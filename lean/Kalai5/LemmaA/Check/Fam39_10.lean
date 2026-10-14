import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_t112_ok : fam39.walk [(10,-1),(0,1),(4,1),(3,1),(2,1)] fam39_t112 = true := by decide +kernel

theorem fam39_t113_ok : fam39.walk [(10,0),(0,1),(4,1),(3,1),(2,1)] fam39_t113 = true := by decide +kernel

theorem fam39_t114_ok : fam39.walk [(14,-1),(10,1),(0,1),(4,1),(3,1),(2,1)] fam39_t114 = true := by decide +kernel

theorem fam39_t115_ok : fam39.walk [(14,0),(10,1),(0,1),(4,1),(3,1),(2,1)] fam39_t115 = true := by decide +kernel

theorem fam39_t116_ok : fam39.walk [(1,-1),(14,1),(10,1),(0,1),(4,1),(3,1),(2,1)] fam39_t116 = true := by decide +kernel

theorem fam39_t117_ok : fam39.walk [(1,0),(14,1),(10,1),(0,1),(4,1),(3,1),(2,1)] fam39_t117 = true := by decide +kernel

theorem fam39_t118_ok : fam39.walk [(1,1),(14,1),(10,1),(0,1),(4,1),(3,1),(2,1)] fam39_t118 = true := by decide +kernel

end Kalai5.LemmaA
