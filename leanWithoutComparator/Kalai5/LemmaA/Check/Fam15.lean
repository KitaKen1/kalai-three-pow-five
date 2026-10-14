import Kalai5.LemmaA.Split
import Kalai5.LemmaA.Check.Fam15_0
import Kalai5.LemmaA.Check.Fam15_1
import Kalai5.LemmaA.Check.Fam15_2

/-! Assembly of the kernel checks of family 15. -/

namespace Kalai5.LemmaA

theorem fam15_u0_ok : fam15.walk [(8,-1),(1,-1),(2,-1)] fam15_u0 = true :=
  Family.walk_branch_of (by decide) fam15_t0_ok fam15_t1_ok fam15_t2_ok

theorem fam15_u1_ok : fam15.walk [(1,-1),(2,-1)] fam15_u1 = true :=
  Family.walk_branch_of (by decide) fam15_u0_ok fam15_t3_ok fam15_t4_ok

theorem fam15_u2_ok : fam15.walk [(8,1),(1,1),(2,-1)] fam15_u2 = true :=
  Family.walk_branch_of (by decide) fam15_t8_ok fam15_t9_ok fam15_t10_ok

theorem fam15_u3_ok : fam15.walk [(1,1),(2,-1)] fam15_u3 = true :=
  Family.walk_branch_of (by decide) fam15_t6_ok fam15_t7_ok fam15_u2_ok

theorem fam15_u4_ok : fam15.walk [(2,-1)] fam15_u4 = true :=
  Family.walk_branch_of (by decide) fam15_u1_ok fam15_t5_ok fam15_u3_ok

theorem fam15_u5_ok : fam15.walk [(8,-1),(1,-1),(2,1)] fam15_u5 = true :=
  Family.walk_branch_of (by decide) fam15_t12_ok fam15_t13_ok fam15_t14_ok

theorem fam15_u6_ok : fam15.walk [(1,-1),(2,1)] fam15_u6 = true :=
  Family.walk_branch_of (by decide) fam15_u5_ok fam15_t15_ok fam15_t16_ok

theorem fam15_u7_ok : fam15.walk [(8,1),(1,1),(2,1)] fam15_u7 = true :=
  Family.walk_branch_of (by decide) fam15_t20_ok fam15_t21_ok fam15_t22_ok

theorem fam15_u8_ok : fam15.walk [(1,1),(2,1)] fam15_u8 = true :=
  Family.walk_branch_of (by decide) fam15_t18_ok fam15_t19_ok fam15_u7_ok

theorem fam15_u9_ok : fam15.walk [(2,1)] fam15_u9 = true :=
  Family.walk_branch_of (by decide) fam15_u6_ok fam15_t17_ok fam15_u8_ok

theorem fam15_u10_ok : fam15.walk [] fam15_u10 = true :=
  Family.walk_branch_of (by decide) fam15_u4_ok fam15_t11_ok fam15_u9_ok

theorem fam15_recs : fam15.facets.all fam15.recOK = true := by
  show (fam15_f0 ++ fam15_f1 ++ fam15_f2 ++ fam15_f3 ++ fam15_f4 ++ fam15_f5 ++ fam15_f6 ++ fam15_f7 ++ fam15_f8).all fam15.recOK = true
  simp only [List.all_append, fam15_f0_ok, fam15_f1_ok, fam15_f2_ok, fam15_f3_ok, fam15_f4_ok, fam15_f5_ok, fam15_f6_ok, fam15_f7_ok, fam15_f8_ok, Bool.and_self]

theorem fam15_check : fam15.check = true :=
  Family.check_of fam15_recs fam15_u10_ok

end Kalai5.LemmaA
