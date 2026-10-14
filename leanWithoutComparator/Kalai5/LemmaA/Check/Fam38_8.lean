import Kalai5.LemmaA.Data.Fam38

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam38_t88_ok : fam38.walk [(10,-1),(8,1),(0,1),(3,1),(2,1)] fam38_t88 = true := by decide +kernel

theorem fam38_t89_ok : fam38.walk [(10,0),(8,1),(0,1),(3,1),(2,1)] fam38_t89 = true := by decide +kernel

theorem fam38_t90_ok : fam38.walk [(11,-1),(10,1),(8,1),(0,1),(3,1),(2,1)] fam38_t90 = true := by decide +kernel

theorem fam38_t91_ok : fam38.walk [(11,0),(10,1),(8,1),(0,1),(3,1),(2,1)] fam38_t91 = true := by decide +kernel

theorem fam38_t92_ok : fam38.walk [(1,-1),(11,1),(10,1),(8,1),(0,1),(3,1),(2,1)] fam38_t92 = true := by decide +kernel

theorem fam38_t93_ok : fam38.walk [(1,0),(11,1),(10,1),(8,1),(0,1),(3,1),(2,1)] fam38_t93 = true := by decide +kernel

theorem fam38_t94_ok : fam38.walk [(1,1),(11,1),(10,1),(8,1),(0,1),(3,1),(2,1)] fam38_t94 = true := by decide +kernel

end Kalai5.LemmaA
