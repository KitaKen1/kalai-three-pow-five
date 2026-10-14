import Kalai5.LemmaA.Split
import Kalai5.LemmaA.Check.Fam0_0
import Kalai5.LemmaA.Check.Fam0_1
import Kalai5.LemmaA.Check.Fam0_2
import Kalai5.LemmaA.Check.Fam0_3

/-! Assembly of the kernel checks of family 0. -/

namespace Kalai5.LemmaA

theorem fam0_u0_ok : fam0.walk [(1,-1),(0,-1),(2,-1)] fam0_u0 = true :=
  Family.walk_branch_of (by decide) fam0_t0_ok fam0_t1_ok fam0_t2_ok

theorem fam0_u1_ok : fam0.walk [(1,1),(0,-1),(2,-1)] fam0_u1 = true :=
  Family.walk_branch_of (by decide) fam0_t4_ok fam0_t5_ok fam0_t6_ok

theorem fam0_u2_ok : fam0.walk [(0,-1),(2,-1)] fam0_u2 = true :=
  Family.walk_branch_of (by decide) fam0_u0_ok fam0_t3_ok fam0_u1_ok

theorem fam0_u3_ok : fam0.walk [(1,-1),(0,1),(2,-1)] fam0_u3 = true :=
  Family.walk_branch_of (by decide) fam0_t8_ok fam0_t9_ok fam0_t10_ok

theorem fam0_u4_ok : fam0.walk [(1,1),(0,1),(2,-1)] fam0_u4 = true :=
  Family.walk_branch_of (by decide) fam0_t12_ok fam0_t13_ok fam0_t14_ok

theorem fam0_u5_ok : fam0.walk [(0,1),(2,-1)] fam0_u5 = true :=
  Family.walk_branch_of (by decide) fam0_u3_ok fam0_t11_ok fam0_u4_ok

theorem fam0_u6_ok : fam0.walk [(2,-1)] fam0_u6 = true :=
  Family.walk_branch_of (by decide) fam0_u2_ok fam0_t7_ok fam0_u5_ok

theorem fam0_u7_ok : fam0.walk [(1,-1),(0,-1),(2,1)] fam0_u7 = true :=
  Family.walk_branch_of (by decide) fam0_t16_ok fam0_t17_ok fam0_t18_ok

theorem fam0_u8_ok : fam0.walk [(1,1),(0,-1),(2,1)] fam0_u8 = true :=
  Family.walk_branch_of (by decide) fam0_t20_ok fam0_t21_ok fam0_t22_ok

theorem fam0_u9_ok : fam0.walk [(0,-1),(2,1)] fam0_u9 = true :=
  Family.walk_branch_of (by decide) fam0_u7_ok fam0_t19_ok fam0_u8_ok

theorem fam0_u10_ok : fam0.walk [(1,-1),(0,1),(2,1)] fam0_u10 = true :=
  Family.walk_branch_of (by decide) fam0_t24_ok fam0_t25_ok fam0_t26_ok

theorem fam0_u11_ok : fam0.walk [(1,1),(0,1),(2,1)] fam0_u11 = true :=
  Family.walk_branch_of (by decide) fam0_t28_ok fam0_t29_ok fam0_t30_ok

theorem fam0_u12_ok : fam0.walk [(0,1),(2,1)] fam0_u12 = true :=
  Family.walk_branch_of (by decide) fam0_u10_ok fam0_t27_ok fam0_u11_ok

theorem fam0_u13_ok : fam0.walk [(2,1)] fam0_u13 = true :=
  Family.walk_branch_of (by decide) fam0_u9_ok fam0_t23_ok fam0_u12_ok

theorem fam0_u14_ok : fam0.walk [] fam0_u14 = true :=
  Family.walk_branch_of (by decide) fam0_u6_ok fam0_t15_ok fam0_u13_ok

theorem fam0_recs : fam0.facets.all fam0.recOK = true := by
  show (fam0_f0 ++ fam0_f1 ++ fam0_f2 ++ fam0_f3 ++ fam0_f4 ++ fam0_f5 ++ fam0_f6 ++ fam0_f7 ++ fam0_f8 ++ fam0_f9).all fam0.recOK = true
  simp only [List.all_append, fam0_f0_ok, fam0_f1_ok, fam0_f2_ok, fam0_f3_ok, fam0_f4_ok, fam0_f5_ok, fam0_f6_ok, fam0_f7_ok, fam0_f8_ok, fam0_f9_ok, Bool.and_self]

theorem fam0_check : fam0.check = true :=
  Family.check_of fam0_recs fam0_u14_ok

end Kalai5.LemmaA
