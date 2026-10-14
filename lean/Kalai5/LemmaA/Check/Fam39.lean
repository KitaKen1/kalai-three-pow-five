import Kalai5.LemmaA.Split
import Kalai5.LemmaA.Check.Fam39_0
import Kalai5.LemmaA.Check.Fam39_1
import Kalai5.LemmaA.Check.Fam39_2
import Kalai5.LemmaA.Check.Fam39_3
import Kalai5.LemmaA.Check.Fam39_4
import Kalai5.LemmaA.Check.Fam39_5
import Kalai5.LemmaA.Check.Fam39_6
import Kalai5.LemmaA.Check.Fam39_7
import Kalai5.LemmaA.Check.Fam39_8
import Kalai5.LemmaA.Check.Fam39_9
import Kalai5.LemmaA.Check.Fam39_10

/-! Assembly of the kernel checks of family 39. -/

namespace Kalai5.LemmaA

theorem fam39_u0_ok : fam39.walk [(14,-1),(10,-1),(0,-1),(4,-1),(3,-1),(2,-1)] fam39_u0 = true :=
  Family.walk_branch_of (by decide) fam39_t0_ok fam39_t1_ok fam39_t2_ok

theorem fam39_u1_ok : fam39.walk [(10,-1),(0,-1),(4,-1),(3,-1),(2,-1)] fam39_u1 = true :=
  Family.walk_branch_of (by decide) fam39_u0_ok fam39_t3_ok fam39_t4_ok

theorem fam39_u2_ok : fam39.walk [(0,-1),(4,-1),(3,-1),(2,-1)] fam39_u2 = true :=
  Family.walk_branch_of (by decide) fam39_u1_ok fam39_t5_ok fam39_t6_ok

theorem fam39_u3_ok : fam39.walk [(4,-1),(3,-1),(2,-1)] fam39_u3 = true :=
  Family.walk_branch_of (by decide) fam39_u2_ok fam39_t7_ok fam39_t8_ok

theorem fam39_u4_ok : fam39.walk [(10,-1),(0,-1),(5,1),(4,1),(3,-1),(2,-1)] fam39_u4 = true :=
  Family.walk_branch_of (by decide) fam39_t12_ok fam39_t13_ok fam39_t14_ok

theorem fam39_u5_ok : fam39.walk [(0,-1),(5,1),(4,1),(3,-1),(2,-1)] fam39_u5 = true :=
  Family.walk_branch_of (by decide) fam39_u4_ok fam39_t15_ok fam39_t16_ok

theorem fam39_u6_ok : fam39.walk [(1,1),(0,1),(5,1),(4,1),(3,-1),(2,-1)] fam39_u6 = true :=
  Family.walk_branch_of (by decide) fam39_t20_ok fam39_t21_ok fam39_t22_ok

theorem fam39_u7_ok : fam39.walk [(0,1),(5,1),(4,1),(3,-1),(2,-1)] fam39_u7 = true :=
  Family.walk_branch_of (by decide) fam39_t18_ok fam39_t19_ok fam39_u6_ok

theorem fam39_u8_ok : fam39.walk [(5,1),(4,1),(3,-1),(2,-1)] fam39_u8 = true :=
  Family.walk_branch_of (by decide) fam39_u5_ok fam39_t17_ok fam39_u7_ok

theorem fam39_u9_ok : fam39.walk [(4,1),(3,-1),(2,-1)] fam39_u9 = true :=
  Family.walk_branch_of (by decide) fam39_t10_ok fam39_t11_ok fam39_u8_ok

theorem fam39_u10_ok : fam39.walk [(3,-1),(2,-1)] fam39_u10 = true :=
  Family.walk_branch_of (by decide) fam39_u3_ok fam39_t9_ok fam39_u9_ok

theorem fam39_u11_ok : fam39.walk [(10,-1),(1,-1),(0,-1),(11,1),(9,-1),(3,0),(2,-1)] fam39_u11 = true :=
  Family.walk_branch_of (by decide) fam39_t25_ok fam39_t26_ok fam39_t27_ok

theorem fam39_u12_ok : fam39.walk [(1,-1),(0,-1),(11,1),(9,-1),(3,0),(2,-1)] fam39_u12 = true :=
  Family.walk_branch_of (by decide) fam39_u11_ok fam39_t28_ok fam39_t29_ok

theorem fam39_u13_ok : fam39.walk [(0,-1),(11,1),(9,-1),(3,0),(2,-1)] fam39_u13 = true :=
  Family.walk_branch_of (by decide) fam39_u12_ok fam39_t30_ok fam39_t31_ok

theorem fam39_u14_ok : fam39.walk [(11,1),(9,-1),(3,0),(2,-1)] fam39_u14 = true :=
  Family.walk_branch_of (by decide) fam39_u13_ok fam39_t32_ok fam39_t33_ok

theorem fam39_u15_ok : fam39.walk [(9,-1),(3,0),(2,-1)] fam39_u15 = true :=
  Family.walk_branch_of (by decide) fam39_t23_ok fam39_t24_ok fam39_u14_ok

theorem fam39_u16_ok : fam39.walk [(3,0),(2,-1)] fam39_u16 = true :=
  Family.walk_branch_of (by decide) fam39_u15_ok fam39_t34_ok fam39_t35_ok

theorem fam39_u17_ok : fam39.walk [(5,-1),(1,-1),(0,-1),(4,-1),(3,1),(2,-1)] fam39_u17 = true :=
  Family.walk_branch_of (by decide) fam39_t36_ok fam39_t37_ok fam39_t38_ok

theorem fam39_u18_ok : fam39.walk [(1,-1),(0,-1),(4,-1),(3,1),(2,-1)] fam39_u18 = true :=
  Family.walk_branch_of (by decide) fam39_u17_ok fam39_t39_ok fam39_t40_ok

theorem fam39_u19_ok : fam39.walk [(0,-1),(4,-1),(3,1),(2,-1)] fam39_u19 = true :=
  Family.walk_branch_of (by decide) fam39_u18_ok fam39_t41_ok fam39_t42_ok

theorem fam39_u20_ok : fam39.walk [(4,-1),(3,1),(2,-1)] fam39_u20 = true :=
  Family.walk_branch_of (by decide) fam39_u19_ok fam39_t43_ok fam39_t44_ok

theorem fam39_u21_ok : fam39.walk [(1,-1),(0,-1),(14,1),(4,1),(3,1),(2,-1)] fam39_u21 = true :=
  Family.walk_branch_of (by decide) fam39_t48_ok fam39_t49_ok fam39_t50_ok

theorem fam39_u22_ok : fam39.walk [(0,-1),(14,1),(4,1),(3,1),(2,-1)] fam39_u22 = true :=
  Family.walk_branch_of (by decide) fam39_u21_ok fam39_t51_ok fam39_t52_ok

theorem fam39_u23_ok : fam39.walk [(10,1),(0,1),(14,1),(4,1),(3,1),(2,-1)] fam39_u23 = true :=
  Family.walk_branch_of (by decide) fam39_t56_ok fam39_t57_ok fam39_t58_ok

theorem fam39_u24_ok : fam39.walk [(0,1),(14,1),(4,1),(3,1),(2,-1)] fam39_u24 = true :=
  Family.walk_branch_of (by decide) fam39_t54_ok fam39_t55_ok fam39_u23_ok

theorem fam39_u25_ok : fam39.walk [(14,1),(4,1),(3,1),(2,-1)] fam39_u25 = true :=
  Family.walk_branch_of (by decide) fam39_u22_ok fam39_t53_ok fam39_u24_ok

theorem fam39_u26_ok : fam39.walk [(4,1),(3,1),(2,-1)] fam39_u26 = true :=
  Family.walk_branch_of (by decide) fam39_t46_ok fam39_t47_ok fam39_u25_ok

theorem fam39_u27_ok : fam39.walk [(3,1),(2,-1)] fam39_u27 = true :=
  Family.walk_branch_of (by decide) fam39_u20_ok fam39_t45_ok fam39_u26_ok

theorem fam39_u28_ok : fam39.walk [(2,-1)] fam39_u28 = true :=
  Family.walk_branch_of (by decide) fam39_u10_ok fam39_u16_ok fam39_u27_ok

theorem fam39_u29_ok : fam39.walk [(10,-1),(0,-1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_u29 = true :=
  Family.walk_branch_of (by decide) fam39_t60_ok fam39_t61_ok fam39_t62_ok

theorem fam39_u30_ok : fam39.walk [(0,-1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_u30 = true :=
  Family.walk_branch_of (by decide) fam39_u29_ok fam39_t63_ok fam39_t64_ok

theorem fam39_u31_ok : fam39.walk [(1,1),(0,1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_u31 = true :=
  Family.walk_branch_of (by decide) fam39_t68_ok fam39_t69_ok fam39_t70_ok

theorem fam39_u32_ok : fam39.walk [(0,1),(14,-1),(4,-1),(3,-1),(2,1)] fam39_u32 = true :=
  Family.walk_branch_of (by decide) fam39_t66_ok fam39_t67_ok fam39_u31_ok

theorem fam39_u33_ok : fam39.walk [(14,-1),(4,-1),(3,-1),(2,1)] fam39_u33 = true :=
  Family.walk_branch_of (by decide) fam39_u30_ok fam39_t65_ok fam39_u32_ok

theorem fam39_u34_ok : fam39.walk [(4,-1),(3,-1),(2,1)] fam39_u34 = true :=
  Family.walk_branch_of (by decide) fam39_u33_ok fam39_t71_ok fam39_t72_ok

theorem fam39_u35_ok : fam39.walk [(5,1),(1,1),(0,1),(4,1),(3,-1),(2,1)] fam39_u35 = true :=
  Family.walk_branch_of (by decide) fam39_t80_ok fam39_t81_ok fam39_t82_ok

theorem fam39_u36_ok : fam39.walk [(1,1),(0,1),(4,1),(3,-1),(2,1)] fam39_u36 = true :=
  Family.walk_branch_of (by decide) fam39_t78_ok fam39_t79_ok fam39_u35_ok

theorem fam39_u37_ok : fam39.walk [(0,1),(4,1),(3,-1),(2,1)] fam39_u37 = true :=
  Family.walk_branch_of (by decide) fam39_t76_ok fam39_t77_ok fam39_u36_ok

theorem fam39_u38_ok : fam39.walk [(4,1),(3,-1),(2,1)] fam39_u38 = true :=
  Family.walk_branch_of (by decide) fam39_t74_ok fam39_t75_ok fam39_u37_ok

theorem fam39_u39_ok : fam39.walk [(3,-1),(2,1)] fam39_u39 = true :=
  Family.walk_branch_of (by decide) fam39_u34_ok fam39_t73_ok fam39_u38_ok

theorem fam39_u40_ok : fam39.walk [(10,1),(1,1),(0,1),(11,-1),(9,1),(3,0),(2,1)] fam39_u40 = true :=
  Family.walk_branch_of (by decide) fam39_t91_ok fam39_t92_ok fam39_t93_ok

theorem fam39_u41_ok : fam39.walk [(1,1),(0,1),(11,-1),(9,1),(3,0),(2,1)] fam39_u41 = true :=
  Family.walk_branch_of (by decide) fam39_t89_ok fam39_t90_ok fam39_u40_ok

theorem fam39_u42_ok : fam39.walk [(0,1),(11,-1),(9,1),(3,0),(2,1)] fam39_u42 = true :=
  Family.walk_branch_of (by decide) fam39_t87_ok fam39_t88_ok fam39_u41_ok

theorem fam39_u43_ok : fam39.walk [(11,-1),(9,1),(3,0),(2,1)] fam39_u43 = true :=
  Family.walk_branch_of (by decide) fam39_t85_ok fam39_t86_ok fam39_u42_ok

theorem fam39_u44_ok : fam39.walk [(9,1),(3,0),(2,1)] fam39_u44 = true :=
  Family.walk_branch_of (by decide) fam39_u43_ok fam39_t94_ok fam39_t95_ok

theorem fam39_u45_ok : fam39.walk [(3,0),(2,1)] fam39_u45 = true :=
  Family.walk_branch_of (by decide) fam39_t83_ok fam39_t84_ok fam39_u44_ok

theorem fam39_u46_ok : fam39.walk [(1,-1),(0,-1),(5,-1),(4,-1),(3,1),(2,1)] fam39_u46 = true :=
  Family.walk_branch_of (by decide) fam39_t96_ok fam39_t97_ok fam39_t98_ok

theorem fam39_u47_ok : fam39.walk [(0,-1),(5,-1),(4,-1),(3,1),(2,1)] fam39_u47 = true :=
  Family.walk_branch_of (by decide) fam39_u46_ok fam39_t99_ok fam39_t100_ok

theorem fam39_u48_ok : fam39.walk [(10,1),(0,1),(5,-1),(4,-1),(3,1),(2,1)] fam39_u48 = true :=
  Family.walk_branch_of (by decide) fam39_t104_ok fam39_t105_ok fam39_t106_ok

theorem fam39_u49_ok : fam39.walk [(0,1),(5,-1),(4,-1),(3,1),(2,1)] fam39_u49 = true :=
  Family.walk_branch_of (by decide) fam39_t102_ok fam39_t103_ok fam39_u48_ok

theorem fam39_u50_ok : fam39.walk [(5,-1),(4,-1),(3,1),(2,1)] fam39_u50 = true :=
  Family.walk_branch_of (by decide) fam39_u47_ok fam39_t101_ok fam39_u49_ok

theorem fam39_u51_ok : fam39.walk [(4,-1),(3,1),(2,1)] fam39_u51 = true :=
  Family.walk_branch_of (by decide) fam39_u50_ok fam39_t107_ok fam39_t108_ok

theorem fam39_u52_ok : fam39.walk [(14,1),(10,1),(0,1),(4,1),(3,1),(2,1)] fam39_u52 = true :=
  Family.walk_branch_of (by decide) fam39_t116_ok fam39_t117_ok fam39_t118_ok

theorem fam39_u53_ok : fam39.walk [(10,1),(0,1),(4,1),(3,1),(2,1)] fam39_u53 = true :=
  Family.walk_branch_of (by decide) fam39_t114_ok fam39_t115_ok fam39_u52_ok

theorem fam39_u54_ok : fam39.walk [(0,1),(4,1),(3,1),(2,1)] fam39_u54 = true :=
  Family.walk_branch_of (by decide) fam39_t112_ok fam39_t113_ok fam39_u53_ok

theorem fam39_u55_ok : fam39.walk [(4,1),(3,1),(2,1)] fam39_u55 = true :=
  Family.walk_branch_of (by decide) fam39_t110_ok fam39_t111_ok fam39_u54_ok

theorem fam39_u56_ok : fam39.walk [(3,1),(2,1)] fam39_u56 = true :=
  Family.walk_branch_of (by decide) fam39_u51_ok fam39_t109_ok fam39_u55_ok

theorem fam39_u57_ok : fam39.walk [(2,1)] fam39_u57 = true :=
  Family.walk_branch_of (by decide) fam39_u39_ok fam39_u45_ok fam39_u56_ok

theorem fam39_u58_ok : fam39.walk [] fam39_u58 = true :=
  Family.walk_branch_of (by decide) fam39_u28_ok fam39_t59_ok fam39_u57_ok

theorem fam39_recs : fam39.facets.all fam39.recOK = true := by
  show (fam39_f0 ++ fam39_f1 ++ fam39_f2 ++ fam39_f3 ++ fam39_f4 ++ fam39_f5 ++ fam39_f6 ++ fam39_f7).all fam39.recOK = true
  simp only [List.all_append, fam39_f0_ok, fam39_f1_ok, fam39_f2_ok, fam39_f3_ok, fam39_f4_ok, fam39_f5_ok, fam39_f6_ok, fam39_f7_ok, Bool.and_self]

theorem fam39_check : fam39.check = true :=
  Family.check_of fam39_recs fam39_u58_ok

end Kalai5.LemmaA
