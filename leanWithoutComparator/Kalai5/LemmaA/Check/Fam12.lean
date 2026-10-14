import Kalai5.LemmaA.Split
import Kalai5.LemmaA.Check.Fam12_0
import Kalai5.LemmaA.Check.Fam12_1
import Kalai5.LemmaA.Check.Fam12_2
import Kalai5.LemmaA.Check.Fam12_3
import Kalai5.LemmaA.Check.Fam12_4
import Kalai5.LemmaA.Check.Fam12_5
import Kalai5.LemmaA.Check.Fam12_6

/-! Assembly of the kernel checks of family 12. -/

namespace Kalai5.LemmaA

theorem fam12_u0_ok : fam12.walk [(8,-1),(6,-1),(0,-1),(1,-1),(2,-1)] fam12_u0 = true :=
  Family.walk_branch_of (by decide) fam12_t0_ok fam12_t1_ok fam12_t2_ok

theorem fam12_u1_ok : fam12.walk [(6,-1),(0,-1),(1,-1),(2,-1)] fam12_u1 = true :=
  Family.walk_branch_of (by decide) fam12_u0_ok fam12_t3_ok fam12_t4_ok

theorem fam12_u2_ok : fam12.walk [(0,-1),(1,-1),(2,-1)] fam12_u2 = true :=
  Family.walk_branch_of (by decide) fam12_u1_ok fam12_t5_ok fam12_t6_ok

theorem fam12_u3_ok : fam12.walk [(8,1),(4,1),(0,1),(1,-1),(2,-1)] fam12_u3 = true :=
  Family.walk_branch_of (by decide) fam12_t12_ok fam12_t13_ok fam12_t14_ok

theorem fam12_u4_ok : fam12.walk [(4,1),(0,1),(1,-1),(2,-1)] fam12_u4 = true :=
  Family.walk_branch_of (by decide) fam12_t10_ok fam12_t11_ok fam12_u3_ok

theorem fam12_u5_ok : fam12.walk [(0,1),(1,-1),(2,-1)] fam12_u5 = true :=
  Family.walk_branch_of (by decide) fam12_t8_ok fam12_t9_ok fam12_u4_ok

theorem fam12_u6_ok : fam12.walk [(1,-1),(2,-1)] fam12_u6 = true :=
  Family.walk_branch_of (by decide) fam12_u2_ok fam12_t7_ok fam12_u5_ok

theorem fam12_u7_ok : fam12.walk [(4,-1),(0,-1),(6,-1),(1,1),(2,-1)] fam12_u7 = true :=
  Family.walk_branch_of (by decide) fam12_t16_ok fam12_t17_ok fam12_t18_ok

theorem fam12_u8_ok : fam12.walk [(0,-1),(6,-1),(1,1),(2,-1)] fam12_u8 = true :=
  Family.walk_branch_of (by decide) fam12_u7_ok fam12_t19_ok fam12_t20_ok

theorem fam12_u9_ok : fam12.walk [(6,-1),(1,1),(2,-1)] fam12_u9 = true :=
  Family.walk_branch_of (by decide) fam12_u8_ok fam12_t21_ok fam12_t22_ok

theorem fam12_u10_ok : fam12.walk [(4,1),(8,1),(6,1),(1,1),(2,-1)] fam12_u10 = true :=
  Family.walk_branch_of (by decide) fam12_t28_ok fam12_t29_ok fam12_t30_ok

theorem fam12_u11_ok : fam12.walk [(8,1),(6,1),(1,1),(2,-1)] fam12_u11 = true :=
  Family.walk_branch_of (by decide) fam12_t26_ok fam12_t27_ok fam12_u10_ok

theorem fam12_u12_ok : fam12.walk [(6,1),(1,1),(2,-1)] fam12_u12 = true :=
  Family.walk_branch_of (by decide) fam12_t24_ok fam12_t25_ok fam12_u11_ok

theorem fam12_u13_ok : fam12.walk [(1,1),(2,-1)] fam12_u13 = true :=
  Family.walk_branch_of (by decide) fam12_u9_ok fam12_t23_ok fam12_u12_ok

theorem fam12_u14_ok : fam12.walk [(2,-1)] fam12_u14 = true :=
  Family.walk_branch_of (by decide) fam12_u6_ok fam12_t15_ok fam12_u13_ok

theorem fam12_u15_ok : fam12.walk [(4,-1),(8,-1),(6,-1),(1,-1),(2,1)] fam12_u15 = true :=
  Family.walk_branch_of (by decide) fam12_t32_ok fam12_t33_ok fam12_t34_ok

theorem fam12_u16_ok : fam12.walk [(8,-1),(6,-1),(1,-1),(2,1)] fam12_u16 = true :=
  Family.walk_branch_of (by decide) fam12_u15_ok fam12_t35_ok fam12_t36_ok

theorem fam12_u17_ok : fam12.walk [(6,-1),(1,-1),(2,1)] fam12_u17 = true :=
  Family.walk_branch_of (by decide) fam12_u16_ok fam12_t37_ok fam12_t38_ok

theorem fam12_u18_ok : fam12.walk [(4,1),(0,1),(6,1),(1,-1),(2,1)] fam12_u18 = true :=
  Family.walk_branch_of (by decide) fam12_t44_ok fam12_t45_ok fam12_t46_ok

theorem fam12_u19_ok : fam12.walk [(0,1),(6,1),(1,-1),(2,1)] fam12_u19 = true :=
  Family.walk_branch_of (by decide) fam12_t42_ok fam12_t43_ok fam12_u18_ok

theorem fam12_u20_ok : fam12.walk [(6,1),(1,-1),(2,1)] fam12_u20 = true :=
  Family.walk_branch_of (by decide) fam12_t40_ok fam12_t41_ok fam12_u19_ok

theorem fam12_u21_ok : fam12.walk [(1,-1),(2,1)] fam12_u21 = true :=
  Family.walk_branch_of (by decide) fam12_u17_ok fam12_t39_ok fam12_u20_ok

theorem fam12_u22_ok : fam12.walk [(8,-1),(4,-1),(0,-1),(1,1),(2,1)] fam12_u22 = true :=
  Family.walk_branch_of (by decide) fam12_t48_ok fam12_t49_ok fam12_t50_ok

theorem fam12_u23_ok : fam12.walk [(4,-1),(0,-1),(1,1),(2,1)] fam12_u23 = true :=
  Family.walk_branch_of (by decide) fam12_u22_ok fam12_t51_ok fam12_t52_ok

theorem fam12_u24_ok : fam12.walk [(0,-1),(1,1),(2,1)] fam12_u24 = true :=
  Family.walk_branch_of (by decide) fam12_u23_ok fam12_t53_ok fam12_t54_ok

theorem fam12_u25_ok : fam12.walk [(8,1),(6,1),(0,1),(1,1),(2,1)] fam12_u25 = true :=
  Family.walk_branch_of (by decide) fam12_t60_ok fam12_t61_ok fam12_t62_ok

theorem fam12_u26_ok : fam12.walk [(6,1),(0,1),(1,1),(2,1)] fam12_u26 = true :=
  Family.walk_branch_of (by decide) fam12_t58_ok fam12_t59_ok fam12_u25_ok

theorem fam12_u27_ok : fam12.walk [(0,1),(1,1),(2,1)] fam12_u27 = true :=
  Family.walk_branch_of (by decide) fam12_t56_ok fam12_t57_ok fam12_u26_ok

theorem fam12_u28_ok : fam12.walk [(1,1),(2,1)] fam12_u28 = true :=
  Family.walk_branch_of (by decide) fam12_u24_ok fam12_t55_ok fam12_u27_ok

theorem fam12_u29_ok : fam12.walk [(2,1)] fam12_u29 = true :=
  Family.walk_branch_of (by decide) fam12_u21_ok fam12_t47_ok fam12_u28_ok

theorem fam12_u30_ok : fam12.walk [] fam12_u30 = true :=
  Family.walk_branch_of (by decide) fam12_u14_ok fam12_t31_ok fam12_u29_ok

theorem fam12_recs : fam12.facets.all fam12.recOK = true := by
  show (fam12_f0 ++ fam12_f1 ++ fam12_f2 ++ fam12_f3 ++ fam12_f4 ++ fam12_f5 ++ fam12_f6 ++ fam12_f7 ++ fam12_f8 ++ fam12_f9).all fam12.recOK = true
  simp only [List.all_append, fam12_f0_ok, fam12_f1_ok, fam12_f2_ok, fam12_f3_ok, fam12_f4_ok, fam12_f5_ok, fam12_f6_ok, fam12_f7_ok, fam12_f8_ok, fam12_f9_ok, Bool.and_self]

theorem fam12_check : fam12.check = true :=
  Family.check_of fam12_recs fam12_u30_ok

end Kalai5.LemmaA
