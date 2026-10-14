import Kalai5.LemmaA.Data.Fam39

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam39_t88_ok : fam39.walk [(1,0),(0,1),(11,-1),(9,1),(3,0),(2,1)] fam39_t88 = true := by decide +kernel

theorem fam39_t89_ok : fam39.walk [(10,-1),(1,1),(0,1),(11,-1),(9,1),(3,0),(2,1)] fam39_t89 = true := by decide +kernel

theorem fam39_t90_ok : fam39.walk [(10,0),(1,1),(0,1),(11,-1),(9,1),(3,0),(2,1)] fam39_t90 = true := by decide +kernel

theorem fam39_t91_ok : fam39.walk [(4,-1),(10,1),(1,1),(0,1),(11,-1),(9,1),(3,0),(2,1)] fam39_t91 = true := by decide +kernel

theorem fam39_t92_ok : fam39.walk [(4,0),(10,1),(1,1),(0,1),(11,-1),(9,1),(3,0),(2,1)] fam39_t92 = true := by decide +kernel

theorem fam39_t93_ok : fam39.walk [(4,1),(10,1),(1,1),(0,1),(11,-1),(9,1),(3,0),(2,1)] fam39_t93 = true := by decide +kernel

theorem fam39_t94_ok : fam39.walk [(11,0),(9,1),(3,0),(2,1)] fam39_t94 = true := by decide +kernel

theorem fam39_t95_ok : fam39.walk [(11,1),(9,1),(3,0),(2,1)] fam39_t95 = true := by decide +kernel

theorem fam39_t96_ok : fam39.walk [(14,-1),(1,-1),(0,-1),(5,-1),(4,-1),(3,1),(2,1)] fam39_t96 = true := by decide +kernel

theorem fam39_t97_ok : fam39.walk [(14,0),(1,-1),(0,-1),(5,-1),(4,-1),(3,1),(2,1)] fam39_t97 = true := by decide +kernel

theorem fam39_t98_ok : fam39.walk [(14,1),(1,-1),(0,-1),(5,-1),(4,-1),(3,1),(2,1)] fam39_t98 = true := by decide +kernel

theorem fam39_t99_ok : fam39.walk [(1,0),(0,-1),(5,-1),(4,-1),(3,1),(2,1)] fam39_t99 = true := by decide +kernel

end Kalai5.LemmaA
