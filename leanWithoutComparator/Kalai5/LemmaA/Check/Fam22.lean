import Kalai5.LemmaA.Split
import Kalai5.LemmaA.Check.Fam22_0
import Kalai5.LemmaA.Check.Fam22_1
import Kalai5.LemmaA.Check.Fam22_2
import Kalai5.LemmaA.Check.Fam22_3
import Kalai5.LemmaA.Check.Fam22_4
import Kalai5.LemmaA.Check.Fam22_5
import Kalai5.LemmaA.Check.Fam22_6
import Kalai5.LemmaA.Check.Fam22_7
import Kalai5.LemmaA.Check.Fam22_8

/-! Assembly of the kernel checks of family 22. -/

namespace Kalai5.LemmaA

theorem fam22_u0_ok : fam22.walk [(8,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam22_u0 = true :=
  Family.walk_branch_of (by decide) fam22_t0_ok fam22_t1_ok fam22_t2_ok

theorem fam22_u1_ok : fam22.walk [(6,-1),(0,-1),(1,-1),(2,-1)] fam22_u1 = true :=
  Family.walk_branch_of (by decide) fam22_u0_ok fam22_t3_ok fam22_t4_ok

theorem fam22_u2_ok : fam22.walk [(0,-1),(1,-1),(2,-1)] fam22_u2 = true :=
  Family.walk_branch_of (by decide) fam22_u1_ok fam22_t5_ok fam22_t6_ok

theorem fam22_u3_ok : fam22.walk [(8,-1),(7,-1),(6,-1),(4,1),(0,0),(1,-1),(2,-1)] fam22_u3 = true :=
  Family.walk_branch_of (by decide) fam22_t9_ok fam22_t10_ok fam22_t11_ok

theorem fam22_u4_ok : fam22.walk [(7,-1),(6,-1),(4,1),(0,0),(1,-1),(2,-1)] fam22_u4 = true :=
  Family.walk_branch_of (by decide) fam22_u3_ok fam22_t12_ok fam22_t13_ok

theorem fam22_u5_ok : fam22.walk [(6,-1),(4,1),(0,0),(1,-1),(2,-1)] fam22_u5 = true :=
  Family.walk_branch_of (by decide) fam22_u4_ok fam22_t14_ok fam22_t15_ok

theorem fam22_u6_ok : fam22.walk [(4,1),(0,0),(1,-1),(2,-1)] fam22_u6 = true :=
  Family.walk_branch_of (by decide) fam22_u5_ok fam22_t16_ok fam22_t17_ok

theorem fam22_u7_ok : fam22.walk [(0,0),(1,-1),(2,-1)] fam22_u7 = true :=
  Family.walk_branch_of (by decide) fam22_t7_ok fam22_t8_ok fam22_u6_ok

theorem fam22_u8_ok : fam22.walk [(4,1),(0,1),(1,-1),(2,-1)] fam22_u8 = true :=
  Family.walk_branch_of (by decide) fam22_t20_ok fam22_t21_ok fam22_t22_ok

theorem fam22_u9_ok : fam22.walk [(0,1),(1,-1),(2,-1)] fam22_u9 = true :=
  Family.walk_branch_of (by decide) fam22_t18_ok fam22_t19_ok fam22_u8_ok

theorem fam22_u10_ok : fam22.walk [(1,-1),(2,-1)] fam22_u10 = true :=
  Family.walk_branch_of (by decide) fam22_u2_ok fam22_u7_ok fam22_u9_ok

theorem fam22_u11_ok : fam22.walk [(6,-1),(0,-1),(8,-1),(1,1),(2,-1)] fam22_u11 = true :=
  Family.walk_branch_of (by decide) fam22_t24_ok fam22_t25_ok fam22_t26_ok

theorem fam22_u12_ok : fam22.walk [(0,-1),(8,-1),(1,1),(2,-1)] fam22_u12 = true :=
  Family.walk_branch_of (by decide) fam22_u11_ok fam22_t27_ok fam22_t28_ok

theorem fam22_u13_ok : fam22.walk [(8,-1),(1,1),(2,-1)] fam22_u13 = true :=
  Family.walk_branch_of (by decide) fam22_u12_ok fam22_t29_ok fam22_t30_ok

theorem fam22_u14_ok : fam22.walk [(20,-1),(14,1),(6,-1),(0,-1),(8,0),(1,1),(2,-1)] fam22_u14 = true :=
  Family.walk_branch_of (by decide) fam22_t33_ok fam22_t34_ok fam22_t35_ok

theorem fam22_u15_ok : fam22.walk [(14,1),(6,-1),(0,-1),(8,0),(1,1),(2,-1)] fam22_u15 = true :=
  Family.walk_branch_of (by decide) fam22_u14_ok fam22_t36_ok fam22_t37_ok

theorem fam22_u16_ok : fam22.walk [(6,-1),(0,-1),(8,0),(1,1),(2,-1)] fam22_u16 = true :=
  Family.walk_branch_of (by decide) fam22_t31_ok fam22_t32_ok fam22_u15_ok

theorem fam22_u17_ok : fam22.walk [(0,-1),(8,0),(1,1),(2,-1)] fam22_u17 = true :=
  Family.walk_branch_of (by decide) fam22_u16_ok fam22_t38_ok fam22_t39_ok

theorem fam22_u18_ok : fam22.walk [(8,0),(1,1),(2,-1)] fam22_u18 = true :=
  Family.walk_branch_of (by decide) fam22_u17_ok fam22_t40_ok fam22_t41_ok

theorem fam22_u19_ok : fam22.walk [(14,1),(8,1),(1,1),(2,-1)] fam22_u19 = true :=
  Family.walk_branch_of (by decide) fam22_t44_ok fam22_t45_ok fam22_t46_ok

theorem fam22_u20_ok : fam22.walk [(8,1),(1,1),(2,-1)] fam22_u20 = true :=
  Family.walk_branch_of (by decide) fam22_t42_ok fam22_t43_ok fam22_u19_ok

theorem fam22_u21_ok : fam22.walk [(1,1),(2,-1)] fam22_u21 = true :=
  Family.walk_branch_of (by decide) fam22_u13_ok fam22_u18_ok fam22_u20_ok

theorem fam22_u22_ok : fam22.walk [(2,-1)] fam22_u22 = true :=
  Family.walk_branch_of (by decide) fam22_u10_ok fam22_t23_ok fam22_u21_ok

theorem fam22_u23_ok : fam22.walk [(14,-1),(8,-1),(1,-1),(2,1)] fam22_u23 = true :=
  Family.walk_branch_of (by decide) fam22_t48_ok fam22_t49_ok fam22_t50_ok

theorem fam22_u24_ok : fam22.walk [(8,-1),(1,-1),(2,1)] fam22_u24 = true :=
  Family.walk_branch_of (by decide) fam22_u23_ok fam22_t51_ok fam22_t52_ok

theorem fam22_u25_ok : fam22.walk [(20,1),(14,-1),(6,1),(0,1),(8,0),(1,-1),(2,1)] fam22_u25 = true :=
  Family.walk_branch_of (by decide) fam22_t59_ok fam22_t60_ok fam22_t61_ok

theorem fam22_u26_ok : fam22.walk [(14,-1),(6,1),(0,1),(8,0),(1,-1),(2,1)] fam22_u26 = true :=
  Family.walk_branch_of (by decide) fam22_t57_ok fam22_t58_ok fam22_u25_ok

theorem fam22_u27_ok : fam22.walk [(6,1),(0,1),(8,0),(1,-1),(2,1)] fam22_u27 = true :=
  Family.walk_branch_of (by decide) fam22_u26_ok fam22_t62_ok fam22_t63_ok

theorem fam22_u28_ok : fam22.walk [(0,1),(8,0),(1,-1),(2,1)] fam22_u28 = true :=
  Family.walk_branch_of (by decide) fam22_t55_ok fam22_t56_ok fam22_u27_ok

theorem fam22_u29_ok : fam22.walk [(8,0),(1,-1),(2,1)] fam22_u29 = true :=
  Family.walk_branch_of (by decide) fam22_t53_ok fam22_t54_ok fam22_u28_ok

theorem fam22_u30_ok : fam22.walk [(6,1),(0,1),(8,1),(1,-1),(2,1)] fam22_u30 = true :=
  Family.walk_branch_of (by decide) fam22_t68_ok fam22_t69_ok fam22_t70_ok

theorem fam22_u31_ok : fam22.walk [(0,1),(8,1),(1,-1),(2,1)] fam22_u31 = true :=
  Family.walk_branch_of (by decide) fam22_t66_ok fam22_t67_ok fam22_u30_ok

theorem fam22_u32_ok : fam22.walk [(8,1),(1,-1),(2,1)] fam22_u32 = true :=
  Family.walk_branch_of (by decide) fam22_t64_ok fam22_t65_ok fam22_u31_ok

theorem fam22_u33_ok : fam22.walk [(1,-1),(2,1)] fam22_u33 = true :=
  Family.walk_branch_of (by decide) fam22_u24_ok fam22_u29_ok fam22_u32_ok

theorem fam22_u34_ok : fam22.walk [(4,-1),(0,-1),(1,1),(2,1)] fam22_u34 = true :=
  Family.walk_branch_of (by decide) fam22_t72_ok fam22_t73_ok fam22_t74_ok

theorem fam22_u35_ok : fam22.walk [(0,-1),(1,1),(2,1)] fam22_u35 = true :=
  Family.walk_branch_of (by decide) fam22_u34_ok fam22_t75_ok fam22_t76_ok

theorem fam22_u36_ok : fam22.walk [(8,1),(7,1),(6,1),(4,-1),(0,0),(1,1),(2,1)] fam22_u36 = true :=
  Family.walk_branch_of (by decide) fam22_t83_ok fam22_t84_ok fam22_t85_ok

theorem fam22_u37_ok : fam22.walk [(7,1),(6,1),(4,-1),(0,0),(1,1),(2,1)] fam22_u37 = true :=
  Family.walk_branch_of (by decide) fam22_t81_ok fam22_t82_ok fam22_u36_ok

theorem fam22_u38_ok : fam22.walk [(6,1),(4,-1),(0,0),(1,1),(2,1)] fam22_u38 = true :=
  Family.walk_branch_of (by decide) fam22_t79_ok fam22_t80_ok fam22_u37_ok

theorem fam22_u39_ok : fam22.walk [(4,-1),(0,0),(1,1),(2,1)] fam22_u39 = true :=
  Family.walk_branch_of (by decide) fam22_t77_ok fam22_t78_ok fam22_u38_ok

theorem fam22_u40_ok : fam22.walk [(0,0),(1,1),(2,1)] fam22_u40 = true :=
  Family.walk_branch_of (by decide) fam22_u39_ok fam22_t86_ok fam22_t87_ok

theorem fam22_u41_ok : fam22.walk [(8,1),(6,1),(0,1),(1,1),(2,1)] fam22_u41 = true :=
  Family.walk_branch_of (by decide) fam22_t92_ok fam22_t93_ok fam22_t94_ok

theorem fam22_u42_ok : fam22.walk [(6,1),(0,1),(1,1),(2,1)] fam22_u42 = true :=
  Family.walk_branch_of (by decide) fam22_t90_ok fam22_t91_ok fam22_u41_ok

theorem fam22_u43_ok : fam22.walk [(0,1),(1,1),(2,1)] fam22_u43 = true :=
  Family.walk_branch_of (by decide) fam22_t88_ok fam22_t89_ok fam22_u42_ok

theorem fam22_u44_ok : fam22.walk [(1,1),(2,1)] fam22_u44 = true :=
  Family.walk_branch_of (by decide) fam22_u35_ok fam22_u40_ok fam22_u43_ok

theorem fam22_u45_ok : fam22.walk [(2,1)] fam22_u45 = true :=
  Family.walk_branch_of (by decide) fam22_u33_ok fam22_t71_ok fam22_u44_ok

theorem fam22_u46_ok : fam22.walk [] fam22_u46 = true :=
  Family.walk_branch_of (by decide) fam22_u22_ok fam22_t47_ok fam22_u45_ok

theorem fam22_recs : fam22.facets.all fam22.recOK = true := by
  show (fam22_f0 ++ fam22_f1 ++ fam22_f2 ++ fam22_f3 ++ fam22_f4 ++ fam22_f5 ++ fam22_f6 ++ fam22_f7).all fam22.recOK = true
  simp only [List.all_append, fam22_f0_ok, fam22_f1_ok, fam22_f2_ok, fam22_f3_ok, fam22_f4_ok, fam22_f5_ok, fam22_f6_ok, fam22_f7_ok, Bool.and_self]

theorem fam22_check : fam22.check = true :=
  Family.check_of fam22_recs fam22_u46_ok

end Kalai5.LemmaA
