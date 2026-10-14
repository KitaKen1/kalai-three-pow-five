import Kalai5.LemmaA.Data.Fam22

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam22_t88_ok : fam22.walk [(6,-1),(0,1),(1,1),(2,1)] fam22_t88 = true := by decide +kernel

theorem fam22_t89_ok : fam22.walk [(6,0),(0,1),(1,1),(2,1)] fam22_t89 = true := by decide +kernel

theorem fam22_t90_ok : fam22.walk [(8,-1),(6,1),(0,1),(1,1),(2,1)] fam22_t90 = true := by decide +kernel

theorem fam22_t91_ok : fam22.walk [(8,0),(6,1),(0,1),(1,1),(2,1)] fam22_t91 = true := by decide +kernel

theorem fam22_t92_ok : fam22.walk [(14,-1),(8,1),(6,1),(0,1),(1,1),(2,1)] fam22_t92 = true := by decide +kernel

theorem fam22_t93_ok : fam22.walk [(14,0),(8,1),(6,1),(0,1),(1,1),(2,1)] fam22_t93 = true := by decide +kernel

theorem fam22_t94_ok : fam22.walk [(14,1),(8,1),(6,1),(0,1),(1,1),(2,1)] fam22_t94 = true := by decide +kernel

end Kalai5.LemmaA
