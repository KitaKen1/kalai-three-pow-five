import Kalai5.A16.Data.Fam33
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 33. -/

namespace Kalai5.A16

theorem fam33_check : fam33.check = true := by decide +kernel

theorem fam33_recs_ok0 : fam33.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam33_recs_ok1 : fam33.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam33_recs_ok2 : fam33.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam33_recs_ok3 : fam33.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam33_recs_ok4 : fam33.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam33_recs_ok5 : fam33.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam33_recs_ok6 : fam33.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam33_recs_ok7 : fam33.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam33_recs_ok8 : fam33.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam33_recs_ok9 : fam33.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam33_recs_ok10 : fam33.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam33_sub0_ok : fam33.subOK 0 = true := by decide +kernel

theorem fam33_sub1_ok : fam33.subOK 1 = true := by decide +kernel

theorem fam33_sub2_ok : fam33.subOK 2 = true := by decide +kernel

theorem fam33_sub3_ok : fam33.subOK 3 = true := by decide +kernel

theorem fam33_sub4_ok : fam33.subOK 4 = true := by decide +kernel

theorem fam33_sub5_ok : fam33.subOK 5 = true := by decide +kernel

theorem fam33_sub6_ok : fam33.subOK 6 = true := by decide +kernel

theorem fam33_sub7_ok : fam33.subOK 7 = true := by decide +kernel

theorem fam33_sub8_ok : fam33.subOK 8 = true := by decide +kernel

theorem fam33_sub9_ok : fam33.subOK 9 = true := by decide +kernel

theorem fam33_sub10_ok : fam33.subOK 10 = true := by decide +kernel

theorem fam33_sub11_ok : fam33.subOK 11 = true := by decide +kernel

theorem fam33_sub12_ok : fam33.subOK 12 = true := by decide +kernel

theorem fam33_sub13_ok : fam33.subOK 13 = true := by decide +kernel

theorem fam33_sub14_ok : fam33.subOK 14 = true := by decide +kernel

theorem fam33_sub15_ok : fam33.subOK 15 = true := by decide +kernel

theorem fam33_sub16_ok : fam33.subOK 16 = true := by decide +kernel

theorem fam33_sub17_ok : fam33.subOK 17 = true := by decide +kernel

theorem fam33_sub18_ok : fam33.subOK 18 = true := by decide +kernel

theorem fam33_sub19_ok : fam33.subOK 19 = true := by decide +kernel

theorem fam33_sub20_ok : fam33.subOK 20 = true := by decide +kernel

theorem fam33_sub21_ok : fam33.subOK 21 = true := by decide +kernel

theorem fam33_sub22_ok : fam33.subOK 22 = true := by decide +kernel

theorem fam33_recs : ∀ r ∈ fam33.recs, fam33.recOK r = true :=
  fam33.recs_of_chunks 11 (fun c hc => by
    interval_cases c
    exacts [fam33_recs_ok0, fam33_recs_ok1, fam33_recs_ok2, fam33_recs_ok3, fam33_recs_ok4, fam33_recs_ok5, fam33_recs_ok6, fam33_recs_ok7, fam33_recs_ok8, fam33_recs_ok9, fam33_recs_ok10])
    (by decide +kernel)

theorem fam33_subs : ∀ k < fam33.subs.length, fam33.subOK k = true := by
  intro k hk
  have h : fam33.subs.length = 23 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam33_sub0_ok, fam33_sub1_ok, fam33_sub2_ok, fam33_sub3_ok, fam33_sub4_ok, fam33_sub5_ok, fam33_sub6_ok, fam33_sub7_ok, fam33_sub8_ok, fam33_sub9_ok, fam33_sub10_ok, fam33_sub11_ok, fam33_sub12_ok, fam33_sub13_ok, fam33_sub14_ok, fam33_sub15_ok, fam33_sub16_ok, fam33_sub17_ok, fam33_sub18_ok, fam33_sub19_ok, fam33_sub20_ok, fam33_sub21_ok, fam33_sub22_ok]

end Kalai5.A16
