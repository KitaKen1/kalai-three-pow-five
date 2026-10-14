import Kalai5.LemmaA.Data.Fam26

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam26_t89_ok : fam26.walk [(6,0),(0,1),(1,1),(2,1)] fam26_t89 = true := by decide +kernel

theorem fam26_t90_ok : fam26.walk [(14,-1),(5,-1),(6,1),(0,1),(1,1),(2,1)] fam26_t90 = true := by decide +kernel

theorem fam26_t91_ok : fam26.walk [(14,0),(5,-1),(6,1),(0,1),(1,1),(2,1)] fam26_t91 = true := by decide +kernel

theorem fam26_t92_ok : fam26.walk [(4,-1),(14,1),(5,-1),(6,1),(0,1),(1,1),(2,1)] fam26_t92 = true := by decide +kernel

theorem fam26_t93_ok : fam26.walk [(4,0),(14,1),(5,-1),(6,1),(0,1),(1,1),(2,1)] fam26_t93 = true := by decide +kernel

theorem fam26_t94_ok : fam26.walk [(4,1),(14,1),(5,-1),(6,1),(0,1),(1,1),(2,1)] fam26_t94 = true := by decide +kernel

theorem fam26_t95_ok : fam26.walk [(3,-1),(5,0),(6,1),(0,1),(1,1),(2,1)] fam26_t95 = true := by decide +kernel

theorem fam26_t96_ok : fam26.walk [(3,0),(5,0),(6,1),(0,1),(1,1),(2,1)] fam26_t96 = true := by decide +kernel

theorem fam26_t97_ok : fam26.walk [(3,1),(5,0),(6,1),(0,1),(1,1),(2,1)] fam26_t97 = true := by decide +kernel

theorem fam26_t98_ok : fam26.walk [(8,-1),(5,1),(6,1),(0,1),(1,1),(2,1)] fam26_t98 = true := by decide +kernel

theorem fam26_t99_ok : fam26.walk [(8,0),(5,1),(6,1),(0,1),(1,1),(2,1)] fam26_t99 = true := by decide +kernel

theorem fam26_t100_ok : fam26.walk [(3,-1),(8,1),(5,1),(6,1),(0,1),(1,1),(2,1)] fam26_t100 = true := by decide +kernel

end Kalai5.LemmaA
