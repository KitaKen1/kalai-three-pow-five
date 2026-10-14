import Kalai5.A16.Data.Fam7
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 7. -/

namespace Kalai5.A16

theorem fam7_check : fam7.check = true := by decide +kernel

theorem fam7_recs_ok0 : fam7.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam7_recs_ok1 : fam7.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam7_recs_ok2 : fam7.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam7_recs_ok3 : fam7.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam7_recs_ok4 : fam7.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam7_recs_ok5 : fam7.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam7_recs_ok6 : fam7.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam7_recs_ok7 : fam7.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam7_recs_ok8 : fam7.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam7_recs_ok9 : fam7.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam7_sub0_ok : fam7.subOK 0 = true := by decide +kernel

theorem fam7_sub1_ok : fam7.subOK 1 = true := by decide +kernel

theorem fam7_sub2_ok : fam7.subOK 2 = true := by decide +kernel

theorem fam7_sub3_ok : fam7.subOK 3 = true := by decide +kernel

theorem fam7_sub4_ok : fam7.subOK 4 = true := by decide +kernel

theorem fam7_sub5_ok : fam7.subOK 5 = true := by decide +kernel

theorem fam7_sub6_ok : fam7.subOK 6 = true := by decide +kernel

theorem fam7_sub7_ok : fam7.subOK 7 = true := by decide +kernel

theorem fam7_sub8_ok : fam7.subOK 8 = true := by decide +kernel

theorem fam7_sub9_ok : fam7.subOK 9 = true := by decide +kernel

theorem fam7_sub10_ok : fam7.subOK 10 = true := by decide +kernel

theorem fam7_sub11_ok : fam7.subOK 11 = true := by decide +kernel

theorem fam7_sub12_ok : fam7.subOK 12 = true := by decide +kernel

theorem fam7_sub13_ok : fam7.subOK 13 = true := by decide +kernel

theorem fam7_recs : ∀ r ∈ fam7.recs, fam7.recOK r = true :=
  fam7.recs_of_chunks 10 (fun c hc => by
    interval_cases c
    exacts [fam7_recs_ok0, fam7_recs_ok1, fam7_recs_ok2, fam7_recs_ok3, fam7_recs_ok4, fam7_recs_ok5, fam7_recs_ok6, fam7_recs_ok7, fam7_recs_ok8, fam7_recs_ok9])
    (by decide +kernel)

theorem fam7_subs : ∀ k < fam7.subs.length, fam7.subOK k = true := by
  intro k hk
  have h : fam7.subs.length = 14 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam7_sub0_ok, fam7_sub1_ok, fam7_sub2_ok, fam7_sub3_ok, fam7_sub4_ok, fam7_sub5_ok, fam7_sub6_ok, fam7_sub7_ok, fam7_sub8_ok, fam7_sub9_ok, fam7_sub10_ok, fam7_sub11_ok, fam7_sub12_ok, fam7_sub13_ok]

end Kalai5.A16
