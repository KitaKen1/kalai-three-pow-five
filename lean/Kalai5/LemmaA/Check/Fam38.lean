import Kalai5.LemmaA.Split
import Kalai5.LemmaA.Check.Fam38_0
import Kalai5.LemmaA.Check.Fam38_1
import Kalai5.LemmaA.Check.Fam38_2
import Kalai5.LemmaA.Check.Fam38_3
import Kalai5.LemmaA.Check.Fam38_4
import Kalai5.LemmaA.Check.Fam38_5
import Kalai5.LemmaA.Check.Fam38_6
import Kalai5.LemmaA.Check.Fam38_7
import Kalai5.LemmaA.Check.Fam38_8

/-! Assembly of the kernel checks of family 38. -/

namespace Kalai5.LemmaA

theorem fam38_u0_ok : fam38.walk [(11,-1),(10,-1),(8,-1),(0,-1),(3,-1),(2,-1)] fam38_u0 = true :=
  Family.walk_branch_of (by decide) fam38_t0_ok fam38_t1_ok fam38_t2_ok

theorem fam38_u1_ok : fam38.walk [(10,-1),(8,-1),(0,-1),(3,-1),(2,-1)] fam38_u1 = true :=
  Family.walk_branch_of (by decide) fam38_u0_ok fam38_t3_ok fam38_t4_ok

theorem fam38_u2_ok : fam38.walk [(8,-1),(0,-1),(3,-1),(2,-1)] fam38_u2 = true :=
  Family.walk_branch_of (by decide) fam38_u1_ok fam38_t5_ok fam38_t6_ok

theorem fam38_u3_ok : fam38.walk [(0,-1),(3,-1),(2,-1)] fam38_u3 = true :=
  Family.walk_branch_of (by decide) fam38_u2_ok fam38_t7_ok fam38_t8_ok

theorem fam38_u4_ok : fam38.walk [(10,-1),(8,-1),(1,1),(0,0),(3,-1),(2,-1)] fam38_u4 = true :=
  Family.walk_branch_of (by decide) fam38_t11_ok fam38_t12_ok fam38_t13_ok

theorem fam38_u5_ok : fam38.walk [(8,-1),(1,1),(0,0),(3,-1),(2,-1)] fam38_u5 = true :=
  Family.walk_branch_of (by decide) fam38_u4_ok fam38_t14_ok fam38_t15_ok

theorem fam38_u6_ok : fam38.walk [(1,1),(0,0),(3,-1),(2,-1)] fam38_u6 = true :=
  Family.walk_branch_of (by decide) fam38_u5_ok fam38_t16_ok fam38_t17_ok

theorem fam38_u7_ok : fam38.walk [(0,0),(3,-1),(2,-1)] fam38_u7 = true :=
  Family.walk_branch_of (by decide) fam38_t9_ok fam38_t10_ok fam38_u6_ok

theorem fam38_u8_ok : fam38.walk [(8,-1),(1,1),(0,1),(3,-1),(2,-1)] fam38_u8 = true :=
  Family.walk_branch_of (by decide) fam38_t20_ok fam38_t21_ok fam38_t22_ok

theorem fam38_u9_ok : fam38.walk [(1,1),(0,1),(3,-1),(2,-1)] fam38_u9 = true :=
  Family.walk_branch_of (by decide) fam38_u8_ok fam38_t23_ok fam38_t24_ok

theorem fam38_u10_ok : fam38.walk [(0,1),(3,-1),(2,-1)] fam38_u10 = true :=
  Family.walk_branch_of (by decide) fam38_t18_ok fam38_t19_ok fam38_u9_ok

theorem fam38_u11_ok : fam38.walk [(3,-1),(2,-1)] fam38_u11 = true :=
  Family.walk_branch_of (by decide) fam38_u3_ok fam38_u7_ok fam38_u10_ok

theorem fam38_u12_ok : fam38.walk [(10,1),(1,1),(0,1),(11,1),(3,0),(2,-1)] fam38_u12 = true :=
  Family.walk_branch_of (by decide) fam38_t33_ok fam38_t34_ok fam38_t35_ok

theorem fam38_u13_ok : fam38.walk [(1,1),(0,1),(11,1),(3,0),(2,-1)] fam38_u13 = true :=
  Family.walk_branch_of (by decide) fam38_t31_ok fam38_t32_ok fam38_u12_ok

theorem fam38_u14_ok : fam38.walk [(0,1),(11,1),(3,0),(2,-1)] fam38_u14 = true :=
  Family.walk_branch_of (by decide) fam38_t29_ok fam38_t30_ok fam38_u13_ok

theorem fam38_u15_ok : fam38.walk [(11,1),(3,0),(2,-1)] fam38_u15 = true :=
  Family.walk_branch_of (by decide) fam38_t27_ok fam38_t28_ok fam38_u14_ok

theorem fam38_u16_ok : fam38.walk [(3,0),(2,-1)] fam38_u16 = true :=
  Family.walk_branch_of (by decide) fam38_t25_ok fam38_t26_ok fam38_u15_ok

theorem fam38_u17_ok : fam38.walk [(10,1),(0,1),(8,1),(11,1),(3,1),(2,-1)] fam38_u17 = true :=
  Family.walk_branch_of (by decide) fam38_t44_ok fam38_t45_ok fam38_t46_ok

theorem fam38_u18_ok : fam38.walk [(0,1),(8,1),(11,1),(3,1),(2,-1)] fam38_u18 = true :=
  Family.walk_branch_of (by decide) fam38_t42_ok fam38_t43_ok fam38_u17_ok

theorem fam38_u19_ok : fam38.walk [(8,1),(11,1),(3,1),(2,-1)] fam38_u19 = true :=
  Family.walk_branch_of (by decide) fam38_t40_ok fam38_t41_ok fam38_u18_ok

theorem fam38_u20_ok : fam38.walk [(11,1),(3,1),(2,-1)] fam38_u20 = true :=
  Family.walk_branch_of (by decide) fam38_t38_ok fam38_t39_ok fam38_u19_ok

theorem fam38_u21_ok : fam38.walk [(3,1),(2,-1)] fam38_u21 = true :=
  Family.walk_branch_of (by decide) fam38_t36_ok fam38_t37_ok fam38_u20_ok

theorem fam38_u22_ok : fam38.walk [(2,-1)] fam38_u22 = true :=
  Family.walk_branch_of (by decide) fam38_u11_ok fam38_u16_ok fam38_u21_ok

theorem fam38_u23_ok : fam38.walk [(10,-1),(0,-1),(8,-1),(11,-1),(3,-1),(2,1)] fam38_u23 = true :=
  Family.walk_branch_of (by decide) fam38_t48_ok fam38_t49_ok fam38_t50_ok

theorem fam38_u24_ok : fam38.walk [(0,-1),(8,-1),(11,-1),(3,-1),(2,1)] fam38_u24 = true :=
  Family.walk_branch_of (by decide) fam38_u23_ok fam38_t51_ok fam38_t52_ok

theorem fam38_u25_ok : fam38.walk [(8,-1),(11,-1),(3,-1),(2,1)] fam38_u25 = true :=
  Family.walk_branch_of (by decide) fam38_u24_ok fam38_t53_ok fam38_t54_ok

theorem fam38_u26_ok : fam38.walk [(11,-1),(3,-1),(2,1)] fam38_u26 = true :=
  Family.walk_branch_of (by decide) fam38_u25_ok fam38_t55_ok fam38_t56_ok

theorem fam38_u27_ok : fam38.walk [(3,-1),(2,1)] fam38_u27 = true :=
  Family.walk_branch_of (by decide) fam38_u26_ok fam38_t57_ok fam38_t58_ok

theorem fam38_u28_ok : fam38.walk [(10,-1),(1,-1),(0,-1),(11,-1),(3,0),(2,1)] fam38_u28 = true :=
  Family.walk_branch_of (by decide) fam38_t59_ok fam38_t60_ok fam38_t61_ok

theorem fam38_u29_ok : fam38.walk [(1,-1),(0,-1),(11,-1),(3,0),(2,1)] fam38_u29 = true :=
  Family.walk_branch_of (by decide) fam38_u28_ok fam38_t62_ok fam38_t63_ok

theorem fam38_u30_ok : fam38.walk [(0,-1),(11,-1),(3,0),(2,1)] fam38_u30 = true :=
  Family.walk_branch_of (by decide) fam38_u29_ok fam38_t64_ok fam38_t65_ok

theorem fam38_u31_ok : fam38.walk [(11,-1),(3,0),(2,1)] fam38_u31 = true :=
  Family.walk_branch_of (by decide) fam38_u30_ok fam38_t66_ok fam38_t67_ok

theorem fam38_u32_ok : fam38.walk [(3,0),(2,1)] fam38_u32 = true :=
  Family.walk_branch_of (by decide) fam38_u31_ok fam38_t68_ok fam38_t69_ok

theorem fam38_u33_ok : fam38.walk [(8,1),(1,-1),(0,-1),(3,1),(2,1)] fam38_u33 = true :=
  Family.walk_branch_of (by decide) fam38_t72_ok fam38_t73_ok fam38_t74_ok

theorem fam38_u34_ok : fam38.walk [(1,-1),(0,-1),(3,1),(2,1)] fam38_u34 = true :=
  Family.walk_branch_of (by decide) fam38_t70_ok fam38_t71_ok fam38_u33_ok

theorem fam38_u35_ok : fam38.walk [(0,-1),(3,1),(2,1)] fam38_u35 = true :=
  Family.walk_branch_of (by decide) fam38_u34_ok fam38_t75_ok fam38_t76_ok

theorem fam38_u36_ok : fam38.walk [(10,1),(8,1),(1,-1),(0,0),(3,1),(2,1)] fam38_u36 = true :=
  Family.walk_branch_of (by decide) fam38_t81_ok fam38_t82_ok fam38_t83_ok

theorem fam38_u37_ok : fam38.walk [(8,1),(1,-1),(0,0),(3,1),(2,1)] fam38_u37 = true :=
  Family.walk_branch_of (by decide) fam38_t79_ok fam38_t80_ok fam38_u36_ok

theorem fam38_u38_ok : fam38.walk [(1,-1),(0,0),(3,1),(2,1)] fam38_u38 = true :=
  Family.walk_branch_of (by decide) fam38_t77_ok fam38_t78_ok fam38_u37_ok

theorem fam38_u39_ok : fam38.walk [(0,0),(3,1),(2,1)] fam38_u39 = true :=
  Family.walk_branch_of (by decide) fam38_u38_ok fam38_t84_ok fam38_t85_ok

theorem fam38_u40_ok : fam38.walk [(11,1),(10,1),(8,1),(0,1),(3,1),(2,1)] fam38_u40 = true :=
  Family.walk_branch_of (by decide) fam38_t92_ok fam38_t93_ok fam38_t94_ok

theorem fam38_u41_ok : fam38.walk [(10,1),(8,1),(0,1),(3,1),(2,1)] fam38_u41 = true :=
  Family.walk_branch_of (by decide) fam38_t90_ok fam38_t91_ok fam38_u40_ok

theorem fam38_u42_ok : fam38.walk [(8,1),(0,1),(3,1),(2,1)] fam38_u42 = true :=
  Family.walk_branch_of (by decide) fam38_t88_ok fam38_t89_ok fam38_u41_ok

theorem fam38_u43_ok : fam38.walk [(0,1),(3,1),(2,1)] fam38_u43 = true :=
  Family.walk_branch_of (by decide) fam38_t86_ok fam38_t87_ok fam38_u42_ok

theorem fam38_u44_ok : fam38.walk [(3,1),(2,1)] fam38_u44 = true :=
  Family.walk_branch_of (by decide) fam38_u35_ok fam38_u39_ok fam38_u43_ok

theorem fam38_u45_ok : fam38.walk [(2,1)] fam38_u45 = true :=
  Family.walk_branch_of (by decide) fam38_u27_ok fam38_u32_ok fam38_u44_ok

theorem fam38_u46_ok : fam38.walk [] fam38_u46 = true :=
  Family.walk_branch_of (by decide) fam38_u22_ok fam38_t47_ok fam38_u45_ok

theorem fam38_recs : fam38.facets.all fam38.recOK = true := by
  show (fam38_f0 ++ fam38_f1 ++ fam38_f2 ++ fam38_f3 ++ fam38_f4 ++ fam38_f5 ++ fam38_f6 ++ fam38_f7).all fam38.recOK = true
  simp only [List.all_append, fam38_f0_ok, fam38_f1_ok, fam38_f2_ok, fam38_f3_ok, fam38_f4_ok, fam38_f5_ok, fam38_f6_ok, fam38_f7_ok, Bool.and_self]

theorem fam38_check : fam38.check = true :=
  Family.check_of fam38_recs fam38_u46_ok

end Kalai5.LemmaA
