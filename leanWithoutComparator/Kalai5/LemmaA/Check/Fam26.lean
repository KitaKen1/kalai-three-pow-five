import Kalai5.LemmaA.Split
import Kalai5.LemmaA.Check.Fam26_0
import Kalai5.LemmaA.Check.Fam26_1
import Kalai5.LemmaA.Check.Fam26_2
import Kalai5.LemmaA.Check.Fam26_3
import Kalai5.LemmaA.Check.Fam26_4
import Kalai5.LemmaA.Check.Fam26_5
import Kalai5.LemmaA.Check.Fam26_6
import Kalai5.LemmaA.Check.Fam26_7
import Kalai5.LemmaA.Check.Fam26_8
import Kalai5.LemmaA.Check.Fam26_9

/-! Assembly of the kernel checks of family 26. -/

namespace Kalai5.LemmaA

theorem fam26_u0_ok : fam26.walk [(8,-1),(5,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_u0 = true :=
  Family.walk_branch_of (by decide) fam26_t0_ok fam26_t1_ok fam26_t2_ok

theorem fam26_u1_ok : fam26.walk [(5,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_u1 = true :=
  Family.walk_branch_of (by decide) fam26_u0_ok fam26_t3_ok fam26_t4_ok

theorem fam26_u2_ok : fam26.walk [(5,0),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_u2 = true :=
  Family.walk_branch_of (by decide) fam26_t5_ok fam26_t6_ok fam26_t7_ok

theorem fam26_u3_ok : fam26.walk [(14,-1),(5,1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_u3 = true :=
  Family.walk_branch_of (by decide) fam26_t8_ok fam26_t9_ok fam26_t10_ok

theorem fam26_u4_ok : fam26.walk [(5,1),(6,-1),(0,-1),(1,-1),(2,-1)] fam26_u4 = true :=
  Family.walk_branch_of (by decide) fam26_u3_ok fam26_t11_ok fam26_t12_ok

theorem fam26_u5_ok : fam26.walk [(6,-1),(0,-1),(1,-1),(2,-1)] fam26_u5 = true :=
  Family.walk_branch_of (by decide) fam26_u1_ok fam26_u2_ok fam26_u4_ok

theorem fam26_u6_ok : fam26.walk [(0,-1),(1,-1),(2,-1)] fam26_u6 = true :=
  Family.walk_branch_of (by decide) fam26_u5_ok fam26_t13_ok fam26_t14_ok

theorem fam26_u7_ok : fam26.walk [(10,1),(4,1),(3,1),(0,1),(1,-1),(2,-1)] fam26_u7 = true :=
  Family.walk_branch_of (by decide) fam26_t22_ok fam26_t23_ok fam26_t24_ok

theorem fam26_u8_ok : fam26.walk [(4,1),(3,1),(0,1),(1,-1),(2,-1)] fam26_u8 = true :=
  Family.walk_branch_of (by decide) fam26_t20_ok fam26_t21_ok fam26_u7_ok

theorem fam26_u9_ok : fam26.walk [(3,1),(0,1),(1,-1),(2,-1)] fam26_u9 = true :=
  Family.walk_branch_of (by decide) fam26_t18_ok fam26_t19_ok fam26_u8_ok

theorem fam26_u10_ok : fam26.walk [(0,1),(1,-1),(2,-1)] fam26_u10 = true :=
  Family.walk_branch_of (by decide) fam26_t16_ok fam26_t17_ok fam26_u9_ok

theorem fam26_u11_ok : fam26.walk [(1,-1),(2,-1)] fam26_u11 = true :=
  Family.walk_branch_of (by decide) fam26_u6_ok fam26_t15_ok fam26_u10_ok

theorem fam26_u12_ok : fam26.walk [(10,-1),(3,-1),(0,-1),(4,-1),(1,1),(2,-1)] fam26_u12 = true :=
  Family.walk_branch_of (by decide) fam26_t26_ok fam26_t27_ok fam26_t28_ok

theorem fam26_u13_ok : fam26.walk [(3,-1),(0,-1),(4,-1),(1,1),(2,-1)] fam26_u13 = true :=
  Family.walk_branch_of (by decide) fam26_u12_ok fam26_t29_ok fam26_t30_ok

theorem fam26_u14_ok : fam26.walk [(0,-1),(4,-1),(1,1),(2,-1)] fam26_u14 = true :=
  Family.walk_branch_of (by decide) fam26_u13_ok fam26_t31_ok fam26_t32_ok

theorem fam26_u15_ok : fam26.walk [(4,-1),(1,1),(2,-1)] fam26_u15 = true :=
  Family.walk_branch_of (by decide) fam26_u14_ok fam26_t33_ok fam26_t34_ok

theorem fam26_u16_ok : fam26.walk [(19,1),(9,-1),(11,1),(4,1),(1,1),(2,-1)] fam26_u16 = true :=
  Family.walk_branch_of (by decide) fam26_t40_ok fam26_t41_ok fam26_t42_ok

theorem fam26_u17_ok : fam26.walk [(9,-1),(11,1),(4,1),(1,1),(2,-1)] fam26_u17 = true :=
  Family.walk_branch_of (by decide) fam26_t38_ok fam26_t39_ok fam26_u16_ok

theorem fam26_u18_ok : fam26.walk [(9,0),(11,1),(4,1),(1,1),(2,-1)] fam26_u18 = true :=
  Family.walk_branch_of (by decide) fam26_t43_ok fam26_t44_ok fam26_t45_ok

theorem fam26_u19_ok : fam26.walk [(6,1),(9,1),(11,1),(4,1),(1,1),(2,-1)] fam26_u19 = true :=
  Family.walk_branch_of (by decide) fam26_t48_ok fam26_t49_ok fam26_t50_ok

theorem fam26_u20_ok : fam26.walk [(9,1),(11,1),(4,1),(1,1),(2,-1)] fam26_u20 = true :=
  Family.walk_branch_of (by decide) fam26_t46_ok fam26_t47_ok fam26_u19_ok

theorem fam26_u21_ok : fam26.walk [(11,1),(4,1),(1,1),(2,-1)] fam26_u21 = true :=
  Family.walk_branch_of (by decide) fam26_u17_ok fam26_u18_ok fam26_u20_ok

theorem fam26_u22_ok : fam26.walk [(4,1),(1,1),(2,-1)] fam26_u22 = true :=
  Family.walk_branch_of (by decide) fam26_t36_ok fam26_t37_ok fam26_u21_ok

theorem fam26_u23_ok : fam26.walk [(1,1),(2,-1)] fam26_u23 = true :=
  Family.walk_branch_of (by decide) fam26_u15_ok fam26_t35_ok fam26_u22_ok

theorem fam26_u24_ok : fam26.walk [(2,-1)] fam26_u24 = true :=
  Family.walk_branch_of (by decide) fam26_u11_ok fam26_t25_ok fam26_u23_ok

theorem fam26_u25_ok : fam26.walk [(6,-1),(9,-1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_u25 = true :=
  Family.walk_branch_of (by decide) fam26_t52_ok fam26_t53_ok fam26_t54_ok

theorem fam26_u26_ok : fam26.walk [(9,-1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_u26 = true :=
  Family.walk_branch_of (by decide) fam26_u25_ok fam26_t55_ok fam26_t56_ok

theorem fam26_u27_ok : fam26.walk [(9,0),(11,-1),(4,-1),(1,-1),(2,1)] fam26_u27 = true :=
  Family.walk_branch_of (by decide) fam26_t57_ok fam26_t58_ok fam26_t59_ok

theorem fam26_u28_ok : fam26.walk [(19,-1),(9,1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_u28 = true :=
  Family.walk_branch_of (by decide) fam26_t60_ok fam26_t61_ok fam26_t62_ok

theorem fam26_u29_ok : fam26.walk [(9,1),(11,-1),(4,-1),(1,-1),(2,1)] fam26_u29 = true :=
  Family.walk_branch_of (by decide) fam26_u28_ok fam26_t63_ok fam26_t64_ok

theorem fam26_u30_ok : fam26.walk [(11,-1),(4,-1),(1,-1),(2,1)] fam26_u30 = true :=
  Family.walk_branch_of (by decide) fam26_u26_ok fam26_u27_ok fam26_u29_ok

theorem fam26_u31_ok : fam26.walk [(4,-1),(1,-1),(2,1)] fam26_u31 = true :=
  Family.walk_branch_of (by decide) fam26_u30_ok fam26_t65_ok fam26_t66_ok

theorem fam26_u32_ok : fam26.walk [(10,1),(3,1),(0,1),(4,1),(1,-1),(2,1)] fam26_u32 = true :=
  Family.walk_branch_of (by decide) fam26_t74_ok fam26_t75_ok fam26_t76_ok

theorem fam26_u33_ok : fam26.walk [(3,1),(0,1),(4,1),(1,-1),(2,1)] fam26_u33 = true :=
  Family.walk_branch_of (by decide) fam26_t72_ok fam26_t73_ok fam26_u32_ok

theorem fam26_u34_ok : fam26.walk [(0,1),(4,1),(1,-1),(2,1)] fam26_u34 = true :=
  Family.walk_branch_of (by decide) fam26_t70_ok fam26_t71_ok fam26_u33_ok

theorem fam26_u35_ok : fam26.walk [(4,1),(1,-1),(2,1)] fam26_u35 = true :=
  Family.walk_branch_of (by decide) fam26_t68_ok fam26_t69_ok fam26_u34_ok

theorem fam26_u36_ok : fam26.walk [(1,-1),(2,1)] fam26_u36 = true :=
  Family.walk_branch_of (by decide) fam26_u31_ok fam26_t67_ok fam26_u35_ok

theorem fam26_u37_ok : fam26.walk [(10,-1),(4,-1),(3,-1),(0,-1),(1,1),(2,1)] fam26_u37 = true :=
  Family.walk_branch_of (by decide) fam26_t78_ok fam26_t79_ok fam26_t80_ok

theorem fam26_u38_ok : fam26.walk [(4,-1),(3,-1),(0,-1),(1,1),(2,1)] fam26_u38 = true :=
  Family.walk_branch_of (by decide) fam26_u37_ok fam26_t81_ok fam26_t82_ok

theorem fam26_u39_ok : fam26.walk [(3,-1),(0,-1),(1,1),(2,1)] fam26_u39 = true :=
  Family.walk_branch_of (by decide) fam26_u38_ok fam26_t83_ok fam26_t84_ok

theorem fam26_u40_ok : fam26.walk [(0,-1),(1,1),(2,1)] fam26_u40 = true :=
  Family.walk_branch_of (by decide) fam26_u39_ok fam26_t85_ok fam26_t86_ok

theorem fam26_u41_ok : fam26.walk [(14,1),(5,-1),(6,1),(0,1),(1,1),(2,1)] fam26_u41 = true :=
  Family.walk_branch_of (by decide) fam26_t92_ok fam26_t93_ok fam26_t94_ok

theorem fam26_u42_ok : fam26.walk [(5,-1),(6,1),(0,1),(1,1),(2,1)] fam26_u42 = true :=
  Family.walk_branch_of (by decide) fam26_t90_ok fam26_t91_ok fam26_u41_ok

theorem fam26_u43_ok : fam26.walk [(5,0),(6,1),(0,1),(1,1),(2,1)] fam26_u43 = true :=
  Family.walk_branch_of (by decide) fam26_t95_ok fam26_t96_ok fam26_t97_ok

theorem fam26_u44_ok : fam26.walk [(8,1),(5,1),(6,1),(0,1),(1,1),(2,1)] fam26_u44 = true :=
  Family.walk_branch_of (by decide) fam26_t100_ok fam26_t101_ok fam26_t102_ok

theorem fam26_u45_ok : fam26.walk [(5,1),(6,1),(0,1),(1,1),(2,1)] fam26_u45 = true :=
  Family.walk_branch_of (by decide) fam26_t98_ok fam26_t99_ok fam26_u44_ok

theorem fam26_u46_ok : fam26.walk [(6,1),(0,1),(1,1),(2,1)] fam26_u46 = true :=
  Family.walk_branch_of (by decide) fam26_u42_ok fam26_u43_ok fam26_u45_ok

theorem fam26_u47_ok : fam26.walk [(0,1),(1,1),(2,1)] fam26_u47 = true :=
  Family.walk_branch_of (by decide) fam26_t88_ok fam26_t89_ok fam26_u46_ok

theorem fam26_u48_ok : fam26.walk [(1,1),(2,1)] fam26_u48 = true :=
  Family.walk_branch_of (by decide) fam26_u40_ok fam26_t87_ok fam26_u47_ok

theorem fam26_u49_ok : fam26.walk [(2,1)] fam26_u49 = true :=
  Family.walk_branch_of (by decide) fam26_u36_ok fam26_t77_ok fam26_u48_ok

theorem fam26_u50_ok : fam26.walk [] fam26_u50 = true :=
  Family.walk_branch_of (by decide) fam26_u24_ok fam26_t51_ok fam26_u49_ok

theorem fam26_recs : fam26.facets.all fam26.recOK = true := by
  show (fam26_f0 ++ fam26_f1 ++ fam26_f2 ++ fam26_f3 ++ fam26_f4 ++ fam26_f5 ++ fam26_f6).all fam26.recOK = true
  simp only [List.all_append, fam26_f0_ok, fam26_f1_ok, fam26_f2_ok, fam26_f3_ok, fam26_f4_ok, fam26_f5_ok, fam26_f6_ok, Bool.and_self]

theorem fam26_check : fam26.check = true :=
  Family.check_of fam26_recs fam26_u50_ok

end Kalai5.LemmaA
