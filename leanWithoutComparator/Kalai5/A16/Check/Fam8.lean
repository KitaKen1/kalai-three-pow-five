import Kalai5.A16.Data.Fam8
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 8. -/

namespace Kalai5.A16

theorem fam8_check : fam8.check = true := by decide +kernel

theorem fam8_recs_ok0 : fam8.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam8_recs_ok1 : fam8.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam8_recs_ok2 : fam8.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam8_recs_ok3 : fam8.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam8_recs_ok4 : fam8.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam8_recs_ok5 : fam8.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam8_recs_ok6 : fam8.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam8_recs_ok7 : fam8.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam8_recs_ok8 : fam8.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam8_recs_ok9 : fam8.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam8_recs_ok10 : fam8.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam8_sub0_ok : fam8.subOK 0 = true := by decide +kernel

theorem fam8_sub1_ok : fam8.subOK 1 = true := by decide +kernel

theorem fam8_sub2_ok : fam8.subOK 2 = true := by decide +kernel

theorem fam8_sub3_ok : fam8.subOK 3 = true := by decide +kernel

theorem fam8_sub4_ok : fam8.subOK 4 = true := by decide +kernel

theorem fam8_sub5_ok : fam8.subOK 5 = true := by decide +kernel

theorem fam8_sub6_ok : fam8.subOK 6 = true := by decide +kernel

theorem fam8_sub7_ok : fam8.subOK 7 = true := by decide +kernel

theorem fam8_sub8_ok : fam8.subOK 8 = true := by decide +kernel

theorem fam8_sub9_ok : fam8.subOK 9 = true := by decide +kernel

theorem fam8_sub10_ok : fam8.subOK 10 = true := by decide +kernel

theorem fam8_sub11_ok : fam8.subOK 11 = true := by decide +kernel

theorem fam8_sub12_ok : fam8.subOK 12 = true := by decide +kernel

theorem fam8_sub13_ok : fam8.subOK 13 = true := by decide +kernel

theorem fam8_sub14_ok : fam8.subOK 14 = true := by decide +kernel

theorem fam8_sub15_ok : fam8.subOK 15 = true := by decide +kernel

theorem fam8_recs : ∀ r ∈ fam8.recs, fam8.recOK r = true :=
  fam8.recs_of_chunks 11 (fun c hc => by
    interval_cases c
    exacts [fam8_recs_ok0, fam8_recs_ok1, fam8_recs_ok2, fam8_recs_ok3, fam8_recs_ok4, fam8_recs_ok5, fam8_recs_ok6, fam8_recs_ok7, fam8_recs_ok8, fam8_recs_ok9, fam8_recs_ok10])
    (by decide +kernel)

theorem fam8_subs : ∀ k < fam8.subs.length, fam8.subOK k = true := by
  intro k hk
  have h : fam8.subs.length = 16 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam8_sub0_ok, fam8_sub1_ok, fam8_sub2_ok, fam8_sub3_ok, fam8_sub4_ok, fam8_sub5_ok, fam8_sub6_ok, fam8_sub7_ok, fam8_sub8_ok, fam8_sub9_ok, fam8_sub10_ok, fam8_sub11_ok, fam8_sub12_ok, fam8_sub13_ok, fam8_sub14_ok, fam8_sub15_ok]

end Kalai5.A16
