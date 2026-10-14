import Kalai5.LemmaA.Split
import Kalai5.LemmaA.Check.Fam32_0
import Kalai5.LemmaA.Check.Fam32_1
import Kalai5.LemmaA.Check.Fam32_2
import Kalai5.LemmaA.Check.Fam32_3
import Kalai5.LemmaA.Check.Fam32_4
import Kalai5.LemmaA.Check.Fam32_5
import Kalai5.LemmaA.Check.Fam32_6
import Kalai5.LemmaA.Check.Fam32_7

/-! Assembly of the kernel checks of family 32. -/

namespace Kalai5.LemmaA

theorem fam32_u0_ok : fam32.walk [(8,-1),(0,-1),(1,1),(3,-1),(2,-1)] fam32_u0 = true :=
  Family.walk_branch_of (by decide) fam32_t2_ok fam32_t3_ok fam32_t4_ok

theorem fam32_u1_ok : fam32.walk [(0,-1),(1,1),(3,-1),(2,-1)] fam32_u1 = true :=
  Family.walk_branch_of (by decide) fam32_u0_ok fam32_t5_ok fam32_t6_ok

theorem fam32_u2_ok : fam32.walk [(7,1),(0,1),(1,1),(3,-1),(2,-1)] fam32_u2 = true :=
  Family.walk_branch_of (by decide) fam32_t10_ok fam32_t11_ok fam32_t12_ok

theorem fam32_u3_ok : fam32.walk [(0,1),(1,1),(3,-1),(2,-1)] fam32_u3 = true :=
  Family.walk_branch_of (by decide) fam32_t8_ok fam32_t9_ok fam32_u2_ok

theorem fam32_u4_ok : fam32.walk [(1,1),(3,-1),(2,-1)] fam32_u4 = true :=
  Family.walk_branch_of (by decide) fam32_u1_ok fam32_t7_ok fam32_u3_ok

theorem fam32_u5_ok : fam32.walk [(3,-1),(2,-1)] fam32_u5 = true :=
  Family.walk_branch_of (by decide) fam32_t0_ok fam32_t1_ok fam32_u4_ok

theorem fam32_u6_ok : fam32.walk [(11,1),(1,1),(0,1),(9,-1),(3,0),(2,-1)] fam32_u6 = true :=
  Family.walk_branch_of (by decide) fam32_t19_ok fam32_t20_ok fam32_t21_ok

theorem fam32_u7_ok : fam32.walk [(1,1),(0,1),(9,-1),(3,0),(2,-1)] fam32_u7 = true :=
  Family.walk_branch_of (by decide) fam32_t17_ok fam32_t18_ok fam32_u6_ok

theorem fam32_u8_ok : fam32.walk [(0,1),(9,-1),(3,0),(2,-1)] fam32_u8 = true :=
  Family.walk_branch_of (by decide) fam32_t15_ok fam32_t16_ok fam32_u7_ok

theorem fam32_u9_ok : fam32.walk [(9,-1),(3,0),(2,-1)] fam32_u9 = true :=
  Family.walk_branch_of (by decide) fam32_t13_ok fam32_t14_ok fam32_u8_ok

theorem fam32_u10_ok : fam32.walk [(3,0),(2,-1)] fam32_u10 = true :=
  Family.walk_branch_of (by decide) fam32_u9_ok fam32_t22_ok fam32_t23_ok

theorem fam32_u11_ok : fam32.walk [(7,-1),(1,-1),(0,1),(3,1),(2,-1)] fam32_u11 = true :=
  Family.walk_branch_of (by decide) fam32_t26_ok fam32_t27_ok fam32_t28_ok

theorem fam32_u12_ok : fam32.walk [(1,-1),(0,1),(3,1),(2,-1)] fam32_u12 = true :=
  Family.walk_branch_of (by decide) fam32_u11_ok fam32_t29_ok fam32_t30_ok

theorem fam32_u13_ok : fam32.walk [(8,1),(1,1),(0,1),(3,1),(2,-1)] fam32_u13 = true :=
  Family.walk_branch_of (by decide) fam32_t34_ok fam32_t35_ok fam32_t36_ok

theorem fam32_u14_ok : fam32.walk [(1,1),(0,1),(3,1),(2,-1)] fam32_u14 = true :=
  Family.walk_branch_of (by decide) fam32_t32_ok fam32_t33_ok fam32_u13_ok

theorem fam32_u15_ok : fam32.walk [(0,1),(3,1),(2,-1)] fam32_u15 = true :=
  Family.walk_branch_of (by decide) fam32_u12_ok fam32_t31_ok fam32_u14_ok

theorem fam32_u16_ok : fam32.walk [(3,1),(2,-1)] fam32_u16 = true :=
  Family.walk_branch_of (by decide) fam32_t24_ok fam32_t25_ok fam32_u15_ok

theorem fam32_u17_ok : fam32.walk [(2,-1)] fam32_u17 = true :=
  Family.walk_branch_of (by decide) fam32_u5_ok fam32_u10_ok fam32_u16_ok

theorem fam32_u18_ok : fam32.walk [(8,-1),(1,-1),(0,-1),(3,-1),(2,1)] fam32_u18 = true :=
  Family.walk_branch_of (by decide) fam32_t38_ok fam32_t39_ok fam32_t40_ok

theorem fam32_u19_ok : fam32.walk [(1,-1),(0,-1),(3,-1),(2,1)] fam32_u19 = true :=
  Family.walk_branch_of (by decide) fam32_u18_ok fam32_t41_ok fam32_t42_ok

theorem fam32_u20_ok : fam32.walk [(7,1),(1,1),(0,-1),(3,-1),(2,1)] fam32_u20 = true :=
  Family.walk_branch_of (by decide) fam32_t46_ok fam32_t47_ok fam32_t48_ok

theorem fam32_u21_ok : fam32.walk [(1,1),(0,-1),(3,-1),(2,1)] fam32_u21 = true :=
  Family.walk_branch_of (by decide) fam32_t44_ok fam32_t45_ok fam32_u20_ok

theorem fam32_u22_ok : fam32.walk [(0,-1),(3,-1),(2,1)] fam32_u22 = true :=
  Family.walk_branch_of (by decide) fam32_u19_ok fam32_t43_ok fam32_u21_ok

theorem fam32_u23_ok : fam32.walk [(3,-1),(2,1)] fam32_u23 = true :=
  Family.walk_branch_of (by decide) fam32_u22_ok fam32_t49_ok fam32_t50_ok

theorem fam32_u24_ok : fam32.walk [(11,-1),(1,-1),(0,-1),(9,1),(3,0),(2,1)] fam32_u24 = true :=
  Family.walk_branch_of (by decide) fam32_t53_ok fam32_t54_ok fam32_t55_ok

theorem fam32_u25_ok : fam32.walk [(1,-1),(0,-1),(9,1),(3,0),(2,1)] fam32_u25 = true :=
  Family.walk_branch_of (by decide) fam32_u24_ok fam32_t56_ok fam32_t57_ok

theorem fam32_u26_ok : fam32.walk [(0,-1),(9,1),(3,0),(2,1)] fam32_u26 = true :=
  Family.walk_branch_of (by decide) fam32_u25_ok fam32_t58_ok fam32_t59_ok

theorem fam32_u27_ok : fam32.walk [(9,1),(3,0),(2,1)] fam32_u27 = true :=
  Family.walk_branch_of (by decide) fam32_u26_ok fam32_t60_ok fam32_t61_ok

theorem fam32_u28_ok : fam32.walk [(3,0),(2,1)] fam32_u28 = true :=
  Family.walk_branch_of (by decide) fam32_t51_ok fam32_t52_ok fam32_u27_ok

theorem fam32_u29_ok : fam32.walk [(7,-1),(0,-1),(1,-1),(3,1),(2,1)] fam32_u29 = true :=
  Family.walk_branch_of (by decide) fam32_t62_ok fam32_t63_ok fam32_t64_ok

theorem fam32_u30_ok : fam32.walk [(0,-1),(1,-1),(3,1),(2,1)] fam32_u30 = true :=
  Family.walk_branch_of (by decide) fam32_u29_ok fam32_t65_ok fam32_t66_ok

theorem fam32_u31_ok : fam32.walk [(8,1),(0,1),(1,-1),(3,1),(2,1)] fam32_u31 = true :=
  Family.walk_branch_of (by decide) fam32_t70_ok fam32_t71_ok fam32_t72_ok

theorem fam32_u32_ok : fam32.walk [(0,1),(1,-1),(3,1),(2,1)] fam32_u32 = true :=
  Family.walk_branch_of (by decide) fam32_t68_ok fam32_t69_ok fam32_u31_ok

theorem fam32_u33_ok : fam32.walk [(1,-1),(3,1),(2,1)] fam32_u33 = true :=
  Family.walk_branch_of (by decide) fam32_u30_ok fam32_t67_ok fam32_u32_ok

theorem fam32_u34_ok : fam32.walk [(3,1),(2,1)] fam32_u34 = true :=
  Family.walk_branch_of (by decide) fam32_u33_ok fam32_t73_ok fam32_t74_ok

theorem fam32_u35_ok : fam32.walk [(2,1)] fam32_u35 = true :=
  Family.walk_branch_of (by decide) fam32_u23_ok fam32_u28_ok fam32_u34_ok

theorem fam32_u36_ok : fam32.walk [] fam32_u36 = true :=
  Family.walk_branch_of (by decide) fam32_u17_ok fam32_t37_ok fam32_u35_ok

theorem fam32_recs : fam32.facets.all fam32.recOK = true := by
  show (fam32_f0 ++ fam32_f1 ++ fam32_f2 ++ fam32_f3 ++ fam32_f4 ++ fam32_f5 ++ fam32_f6 ++ fam32_f7 ++ fam32_f8 ++ fam32_f9).all fam32.recOK = true
  simp only [List.all_append, fam32_f0_ok, fam32_f1_ok, fam32_f2_ok, fam32_f3_ok, fam32_f4_ok, fam32_f5_ok, fam32_f6_ok, fam32_f7_ok, fam32_f8_ok, fam32_f9_ok, Bool.and_self]

theorem fam32_check : fam32.check = true :=
  Family.check_of fam32_recs fam32_u36_ok

end Kalai5.LemmaA
