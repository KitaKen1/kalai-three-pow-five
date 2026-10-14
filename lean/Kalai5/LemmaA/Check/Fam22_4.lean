import Kalai5.LemmaA.Data.Fam22

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem fam22_t40_ok : fam22.walk [(0,0),(8,0),(1,1),(2,-1)] fam22_t40 = true := by decide +kernel

theorem fam22_t41_ok : fam22.walk [(0,1),(8,0),(1,1),(2,-1)] fam22_t41 = true := by decide +kernel

theorem fam22_t42_ok : fam22.walk [(14,-1),(8,1),(1,1),(2,-1)] fam22_t42 = true := by decide +kernel

theorem fam22_t43_ok : fam22.walk [(14,0),(8,1),(1,1),(2,-1)] fam22_t43 = true := by decide +kernel

theorem fam22_t44_ok : fam22.walk [(11,-1),(14,1),(8,1),(1,1),(2,-1)] fam22_t44 = true := by decide +kernel

theorem fam22_t45_ok : fam22.walk [(11,0),(14,1),(8,1),(1,1),(2,-1)] fam22_t45 = true := by decide +kernel

theorem fam22_t46_ok : fam22.walk [(11,1),(14,1),(8,1),(1,1),(2,-1)] fam22_t46 = true := by decide +kernel

theorem fam22_t47_ok : fam22.walk [(2,0)] fam22_t47 = true := by decide +kernel

theorem fam22_t48_ok : fam22.walk [(11,-1),(14,-1),(8,-1),(1,-1),(2,1)] fam22_t48 = true := by decide +kernel

theorem fam22_t49_ok : fam22.walk [(11,0),(14,-1),(8,-1),(1,-1),(2,1)] fam22_t49 = true := by decide +kernel

theorem fam22_t50_ok : fam22.walk [(11,1),(14,-1),(8,-1),(1,-1),(2,1)] fam22_t50 = true := by decide +kernel

theorem fam22_t51_ok : fam22.walk [(14,0),(8,-1),(1,-1),(2,1)] fam22_t51 = true := by decide +kernel

end Kalai5.LemmaA
