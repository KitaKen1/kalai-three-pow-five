import Kalai5.LemmaA.Split
import Kalai5.LemmaA.Check.Fam44_0
import Kalai5.LemmaA.Check.Fam44_1
import Kalai5.LemmaA.Check.Fam44_2
import Kalai5.LemmaA.Check.Fam44_3
import Kalai5.LemmaA.Check.Fam44_4
import Kalai5.LemmaA.Check.Fam44_5
import Kalai5.LemmaA.Check.Fam44_6
import Kalai5.LemmaA.Check.Fam44_7
import Kalai5.LemmaA.Check.Fam44_8
import Kalai5.LemmaA.Check.Fam44_9

/-! Assembly of the kernel checks of family 44. -/

namespace Kalai5.LemmaA

theorem fam44_u0_ok : fam44.walk [(5,1),(9,-1),(2,-1),(0,-1),(1,-1),(3,-1)] fam44_u0 = true :=
  Family.walk_branch_of (by decide) fam44_t2_ok fam44_t3_ok fam44_t4_ok

theorem fam44_u1_ok : fam44.walk [(9,-1),(2,-1),(0,-1),(1,-1),(3,-1)] fam44_u1 = true :=
  Family.walk_branch_of (by decide) fam44_t0_ok fam44_t1_ok fam44_u0_ok

theorem fam44_u2_ok : fam44.walk [(2,-1),(0,-1),(1,-1),(3,-1)] fam44_u2 = true :=
  Family.walk_branch_of (by decide) fam44_u1_ok fam44_t5_ok fam44_t6_ok

theorem fam44_u3_ok : fam44.walk [(0,-1),(1,-1),(3,-1)] fam44_u3 = true :=
  Family.walk_branch_of (by decide) fam44_u2_ok fam44_t7_ok fam44_t8_ok

theorem fam44_u4_ok : fam44.walk [(1,-1),(3,-1)] fam44_u4 = true :=
  Family.walk_branch_of (by decide) fam44_u3_ok fam44_t9_ok fam44_t10_ok

theorem fam44_u5_ok : fam44.walk [(0,-1),(1,0),(3,-1)] fam44_u5 = true :=
  Family.walk_branch_of (by decide) fam44_t11_ok fam44_t12_ok fam44_t13_ok

theorem fam44_u6_ok : fam44.walk [(1,0),(3,-1)] fam44_u6 = true :=
  Family.walk_branch_of (by decide) fam44_u5_ok fam44_t14_ok fam44_t15_ok

theorem fam44_u7_ok : fam44.walk [(13,-1),(4,-1),(2,1),(5,-1),(1,1),(3,-1)] fam44_u7 = true :=
  Family.walk_branch_of (by decide) fam44_t18_ok fam44_t19_ok fam44_t20_ok

theorem fam44_u8_ok : fam44.walk [(4,-1),(2,1),(5,-1),(1,1),(3,-1)] fam44_u8 = true :=
  Family.walk_branch_of (by decide) fam44_u7_ok fam44_t21_ok fam44_t22_ok

theorem fam44_u9_ok : fam44.walk [(2,1),(5,-1),(1,1),(3,-1)] fam44_u9 = true :=
  Family.walk_branch_of (by decide) fam44_u8_ok fam44_t23_ok fam44_t24_ok

theorem fam44_u10_ok : fam44.walk [(5,-1),(1,1),(3,-1)] fam44_u10 = true :=
  Family.walk_branch_of (by decide) fam44_t16_ok fam44_t17_ok fam44_u9_ok

theorem fam44_u11_ok : fam44.walk [(2,1),(13,-1),(4,-1),(5,1),(1,1),(3,-1)] fam44_u11 = true :=
  Family.walk_branch_of (by decide) fam44_t28_ok fam44_t29_ok fam44_t30_ok

theorem fam44_u12_ok : fam44.walk [(13,-1),(4,-1),(5,1),(1,1),(3,-1)] fam44_u12 = true :=
  Family.walk_branch_of (by decide) fam44_t26_ok fam44_t27_ok fam44_u11_ok

theorem fam44_u13_ok : fam44.walk [(4,-1),(5,1),(1,1),(3,-1)] fam44_u13 = true :=
  Family.walk_branch_of (by decide) fam44_u12_ok fam44_t31_ok fam44_t32_ok

theorem fam44_u14_ok : fam44.walk [(13,-1),(7,1),(4,0),(5,1),(1,1),(3,-1)] fam44_u14 = true :=
  Family.walk_branch_of (by decide) fam44_t35_ok fam44_t36_ok fam44_t37_ok

theorem fam44_u15_ok : fam44.walk [(7,1),(4,0),(5,1),(1,1),(3,-1)] fam44_u15 = true :=
  Family.walk_branch_of (by decide) fam44_u14_ok fam44_t38_ok fam44_t39_ok

theorem fam44_u16_ok : fam44.walk [(4,0),(5,1),(1,1),(3,-1)] fam44_u16 = true :=
  Family.walk_branch_of (by decide) fam44_t33_ok fam44_t34_ok fam44_u15_ok

theorem fam44_u17_ok : fam44.walk [(0,1),(7,1),(4,1),(5,1),(1,1),(3,-1)] fam44_u17 = true :=
  Family.walk_branch_of (by decide) fam44_t44_ok fam44_t45_ok fam44_t46_ok

theorem fam44_u18_ok : fam44.walk [(7,1),(4,1),(5,1),(1,1),(3,-1)] fam44_u18 = true :=
  Family.walk_branch_of (by decide) fam44_t42_ok fam44_t43_ok fam44_u17_ok

theorem fam44_u19_ok : fam44.walk [(4,1),(5,1),(1,1),(3,-1)] fam44_u19 = true :=
  Family.walk_branch_of (by decide) fam44_t40_ok fam44_t41_ok fam44_u18_ok

theorem fam44_u20_ok : fam44.walk [(5,1),(1,1),(3,-1)] fam44_u20 = true :=
  Family.walk_branch_of (by decide) fam44_u13_ok fam44_u16_ok fam44_u19_ok

theorem fam44_u21_ok : fam44.walk [(1,1),(3,-1)] fam44_u21 = true :=
  Family.walk_branch_of (by decide) fam44_u10_ok fam44_t25_ok fam44_u20_ok

theorem fam44_u22_ok : fam44.walk [(3,-1)] fam44_u22 = true :=
  Family.walk_branch_of (by decide) fam44_u4_ok fam44_u6_ok fam44_u21_ok

theorem fam44_u23_ok : fam44.walk [(0,-1),(1,-1),(3,0)] fam44_u23 = true :=
  Family.walk_branch_of (by decide) fam44_t47_ok fam44_t48_ok fam44_t49_ok

theorem fam44_u24_ok : fam44.walk [(1,-1),(3,0)] fam44_u24 = true :=
  Family.walk_branch_of (by decide) fam44_u23_ok fam44_t50_ok fam44_t51_ok

theorem fam44_u25_ok : fam44.walk [(0,1),(1,1),(3,0)] fam44_u25 = true :=
  Family.walk_branch_of (by decide) fam44_t55_ok fam44_t56_ok fam44_t57_ok

theorem fam44_u26_ok : fam44.walk [(1,1),(3,0)] fam44_u26 = true :=
  Family.walk_branch_of (by decide) fam44_t53_ok fam44_t54_ok fam44_u25_ok

theorem fam44_u27_ok : fam44.walk [(3,0)] fam44_u27 = true :=
  Family.walk_branch_of (by decide) fam44_u24_ok fam44_t52_ok fam44_u26_ok

theorem fam44_u28_ok : fam44.walk [(0,-1),(7,-1),(4,-1),(5,-1),(1,-1),(3,1)] fam44_u28 = true :=
  Family.walk_branch_of (by decide) fam44_t58_ok fam44_t59_ok fam44_t60_ok

theorem fam44_u29_ok : fam44.walk [(7,-1),(4,-1),(5,-1),(1,-1),(3,1)] fam44_u29 = true :=
  Family.walk_branch_of (by decide) fam44_u28_ok fam44_t61_ok fam44_t62_ok

theorem fam44_u30_ok : fam44.walk [(4,-1),(5,-1),(1,-1),(3,1)] fam44_u30 = true :=
  Family.walk_branch_of (by decide) fam44_u29_ok fam44_t63_ok fam44_t64_ok

theorem fam44_u31_ok : fam44.walk [(13,1),(7,-1),(4,0),(5,-1),(1,-1),(3,1)] fam44_u31 = true :=
  Family.walk_branch_of (by decide) fam44_t67_ok fam44_t68_ok fam44_t69_ok

theorem fam44_u32_ok : fam44.walk [(7,-1),(4,0),(5,-1),(1,-1),(3,1)] fam44_u32 = true :=
  Family.walk_branch_of (by decide) fam44_t65_ok fam44_t66_ok fam44_u31_ok

theorem fam44_u33_ok : fam44.walk [(4,0),(5,-1),(1,-1),(3,1)] fam44_u33 = true :=
  Family.walk_branch_of (by decide) fam44_u32_ok fam44_t70_ok fam44_t71_ok

theorem fam44_u34_ok : fam44.walk [(2,-1),(13,1),(4,1),(5,-1),(1,-1),(3,1)] fam44_u34 = true :=
  Family.walk_branch_of (by decide) fam44_t74_ok fam44_t75_ok fam44_t76_ok

theorem fam44_u35_ok : fam44.walk [(13,1),(4,1),(5,-1),(1,-1),(3,1)] fam44_u35 = true :=
  Family.walk_branch_of (by decide) fam44_u34_ok fam44_t77_ok fam44_t78_ok

theorem fam44_u36_ok : fam44.walk [(4,1),(5,-1),(1,-1),(3,1)] fam44_u36 = true :=
  Family.walk_branch_of (by decide) fam44_t72_ok fam44_t73_ok fam44_u35_ok

theorem fam44_u37_ok : fam44.walk [(5,-1),(1,-1),(3,1)] fam44_u37 = true :=
  Family.walk_branch_of (by decide) fam44_u30_ok fam44_u33_ok fam44_u36_ok

theorem fam44_u38_ok : fam44.walk [(13,1),(4,1),(2,-1),(5,1),(1,-1),(3,1)] fam44_u38 = true :=
  Family.walk_branch_of (by decide) fam44_t84_ok fam44_t85_ok fam44_t86_ok

theorem fam44_u39_ok : fam44.walk [(4,1),(2,-1),(5,1),(1,-1),(3,1)] fam44_u39 = true :=
  Family.walk_branch_of (by decide) fam44_t82_ok fam44_t83_ok fam44_u38_ok

theorem fam44_u40_ok : fam44.walk [(2,-1),(5,1),(1,-1),(3,1)] fam44_u40 = true :=
  Family.walk_branch_of (by decide) fam44_t80_ok fam44_t81_ok fam44_u39_ok

theorem fam44_u41_ok : fam44.walk [(5,1),(1,-1),(3,1)] fam44_u41 = true :=
  Family.walk_branch_of (by decide) fam44_u40_ok fam44_t87_ok fam44_t88_ok

theorem fam44_u42_ok : fam44.walk [(1,-1),(3,1)] fam44_u42 = true :=
  Family.walk_branch_of (by decide) fam44_u37_ok fam44_t79_ok fam44_u41_ok

theorem fam44_u43_ok : fam44.walk [(0,1),(1,0),(3,1)] fam44_u43 = true :=
  Family.walk_branch_of (by decide) fam44_t91_ok fam44_t92_ok fam44_t93_ok

theorem fam44_u44_ok : fam44.walk [(1,0),(3,1)] fam44_u44 = true :=
  Family.walk_branch_of (by decide) fam44_t89_ok fam44_t90_ok fam44_u43_ok

theorem fam44_u45_ok : fam44.walk [(5,-1),(9,1),(2,1),(0,1),(1,1),(3,1)] fam44_u45 = true :=
  Family.walk_branch_of (by decide) fam44_t100_ok fam44_t101_ok fam44_t102_ok

theorem fam44_u46_ok : fam44.walk [(9,1),(2,1),(0,1),(1,1),(3,1)] fam44_u46 = true :=
  Family.walk_branch_of (by decide) fam44_u45_ok fam44_t103_ok fam44_t104_ok

theorem fam44_u47_ok : fam44.walk [(2,1),(0,1),(1,1),(3,1)] fam44_u47 = true :=
  Family.walk_branch_of (by decide) fam44_t98_ok fam44_t99_ok fam44_u46_ok

theorem fam44_u48_ok : fam44.walk [(0,1),(1,1),(3,1)] fam44_u48 = true :=
  Family.walk_branch_of (by decide) fam44_t96_ok fam44_t97_ok fam44_u47_ok

theorem fam44_u49_ok : fam44.walk [(1,1),(3,1)] fam44_u49 = true :=
  Family.walk_branch_of (by decide) fam44_t94_ok fam44_t95_ok fam44_u48_ok

theorem fam44_u50_ok : fam44.walk [(3,1)] fam44_u50 = true :=
  Family.walk_branch_of (by decide) fam44_u42_ok fam44_u44_ok fam44_u49_ok

theorem fam44_u51_ok : fam44.walk [] fam44_u51 = true :=
  Family.walk_branch_of (by decide) fam44_u22_ok fam44_u27_ok fam44_u50_ok

theorem fam44_recs : fam44.facets.all fam44.recOK = true := by
  show (fam44_f0 ++ fam44_f1 ++ fam44_f2 ++ fam44_f3 ++ fam44_f4 ++ fam44_f5 ++ fam44_f6 ++ fam44_f7 ++ fam44_f8).all fam44.recOK = true
  simp only [List.all_append, fam44_f0_ok, fam44_f1_ok, fam44_f2_ok, fam44_f3_ok, fam44_f4_ok, fam44_f5_ok, fam44_f6_ok, fam44_f7_ok, fam44_f8_ok, Bool.and_self]

theorem fam44_check : fam44.check = true :=
  Family.check_of fam44_recs fam44_u51_ok

end Kalai5.LemmaA
