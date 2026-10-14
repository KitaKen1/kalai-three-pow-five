import Kalai5.A16.Data.Fam0
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 0. -/

namespace Kalai5.A16

theorem fam0_check : fam0.check = true := by decide +kernel

theorem fam0_recs_ok0 : fam0.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam0_recs_ok1 : fam0.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam0_recs_ok2 : fam0.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam0_recs_ok3 : fam0.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam0_recs_ok4 : fam0.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam0_recs_ok5 : fam0.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam0_recs_ok6 : fam0.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam0_recs_ok7 : fam0.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam0_sub0_ok : fam0.subOK 0 = true := by decide +kernel

theorem fam0_sub1_ok : fam0.subOK 1 = true := by decide +kernel

theorem fam0_sub2_ok : fam0.subOK 2 = true := by decide +kernel

theorem fam0_sub3_ok : fam0.subOK 3 = true := by decide +kernel

theorem fam0_sub4_ok : fam0.subOK 4 = true := by decide +kernel

theorem fam0_sub5_ok : fam0.subOK 5 = true := by decide +kernel

theorem fam0_sub6_ok : fam0.subOK 6 = true := by decide +kernel

theorem fam0_sub7_ok : fam0.subOK 7 = true := by decide +kernel

theorem fam0_sub8_ok : fam0.subOK 8 = true := by decide +kernel

theorem fam0_sub9_ok : fam0.subOK 9 = true := by decide +kernel

theorem fam0_sub10_ok : fam0.subOK 10 = true := by decide +kernel

theorem fam0_sub11_ok : fam0.subOK 11 = true := by decide +kernel

theorem fam0_sub12_ok : fam0.subOK 12 = true := by decide +kernel

theorem fam0_sub13_ok : fam0.subOK 13 = true := by decide +kernel

theorem fam0_sub14_ok : fam0.subOK 14 = true := by decide +kernel

theorem fam0_sub15_ok : fam0.subOK 15 = true := by decide +kernel

theorem fam0_sub16_ok : fam0.subOK 16 = true := by decide +kernel

theorem fam0_sub17_ok : fam0.subOK 17 = true := by decide +kernel

theorem fam0_sub18_ok : fam0.subOK 18 = true := by decide +kernel

theorem fam0_sub19_ok : fam0.subOK 19 = true := by decide +kernel

theorem fam0_recs : ∀ r ∈ fam0.recs, fam0.recOK r = true :=
  fam0.recs_of_chunks 8 (fun c hc => by
    interval_cases c
    exacts [fam0_recs_ok0, fam0_recs_ok1, fam0_recs_ok2, fam0_recs_ok3, fam0_recs_ok4, fam0_recs_ok5, fam0_recs_ok6, fam0_recs_ok7])
    (by decide +kernel)

theorem fam0_subs : ∀ k < fam0.subs.length, fam0.subOK k = true := by
  intro k hk
  have h : fam0.subs.length = 20 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam0_sub0_ok, fam0_sub1_ok, fam0_sub2_ok, fam0_sub3_ok, fam0_sub4_ok, fam0_sub5_ok, fam0_sub6_ok, fam0_sub7_ok, fam0_sub8_ok, fam0_sub9_ok, fam0_sub10_ok, fam0_sub11_ok, fam0_sub12_ok, fam0_sub13_ok, fam0_sub14_ok, fam0_sub15_ok, fam0_sub16_ok, fam0_sub17_ok, fam0_sub18_ok, fam0_sub19_ok]

end Kalai5.A16
