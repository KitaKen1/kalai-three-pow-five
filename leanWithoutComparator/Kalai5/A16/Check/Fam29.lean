import Kalai5.A16.Data.Fam29
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 29. -/

namespace Kalai5.A16

theorem fam29_check : fam29.check = true := by decide +kernel

theorem fam29_recs_ok0 : fam29.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam29_recs_ok1 : fam29.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam29_recs_ok2 : fam29.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam29_recs_ok3 : fam29.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam29_recs_ok4 : fam29.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam29_recs_ok5 : fam29.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam29_recs_ok6 : fam29.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam29_recs_ok7 : fam29.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam29_recs_ok8 : fam29.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam29_recs_ok9 : fam29.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam29_recs_ok10 : fam29.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam29_sub0_ok : fam29.subOK 0 = true := by decide +kernel

theorem fam29_sub1_ok : fam29.subOK 1 = true := by decide +kernel

theorem fam29_sub2_ok : fam29.subOK 2 = true := by decide +kernel

theorem fam29_sub3_ok : fam29.subOK 3 = true := by decide +kernel

theorem fam29_sub4_ok : fam29.subOK 4 = true := by decide +kernel

theorem fam29_sub5_ok : fam29.subOK 5 = true := by decide +kernel

theorem fam29_sub6_ok : fam29.subOK 6 = true := by decide +kernel

theorem fam29_sub7_ok : fam29.subOK 7 = true := by decide +kernel

theorem fam29_sub8_ok : fam29.subOK 8 = true := by decide +kernel

theorem fam29_sub9_ok : fam29.subOK 9 = true := by decide +kernel

theorem fam29_sub10_ok : fam29.subOK 10 = true := by decide +kernel

theorem fam29_sub11_ok : fam29.subOK 11 = true := by decide +kernel

theorem fam29_sub12_ok : fam29.subOK 12 = true := by decide +kernel

theorem fam29_sub13_ok : fam29.subOK 13 = true := by decide +kernel

theorem fam29_sub14_ok : fam29.subOK 14 = true := by decide +kernel

theorem fam29_sub15_ok : fam29.subOK 15 = true := by decide +kernel

theorem fam29_sub16_ok : fam29.subOK 16 = true := by decide +kernel

theorem fam29_sub17_ok : fam29.subOK 17 = true := by decide +kernel

theorem fam29_sub18_ok : fam29.subOK 18 = true := by decide +kernel

theorem fam29_sub19_ok : fam29.subOK 19 = true := by decide +kernel

theorem fam29_sub20_ok : fam29.subOK 20 = true := by decide +kernel

theorem fam29_sub21_ok : fam29.subOK 21 = true := by decide +kernel

theorem fam29_sub22_ok : fam29.subOK 22 = true := by decide +kernel

theorem fam29_sub23_ok : fam29.subOK 23 = true := by decide +kernel

theorem fam29_sub24_ok : fam29.subOK 24 = true := by decide +kernel

theorem fam29_sub25_ok : fam29.subOK 25 = true := by decide +kernel

theorem fam29_sub26_ok : fam29.subOK 26 = true := by decide +kernel

theorem fam29_sub27_ok : fam29.subOK 27 = true := by decide +kernel

theorem fam29_recs : ∀ r ∈ fam29.recs, fam29.recOK r = true :=
  fam29.recs_of_chunks 11 (fun c hc => by
    interval_cases c
    exacts [fam29_recs_ok0, fam29_recs_ok1, fam29_recs_ok2, fam29_recs_ok3, fam29_recs_ok4, fam29_recs_ok5, fam29_recs_ok6, fam29_recs_ok7, fam29_recs_ok8, fam29_recs_ok9, fam29_recs_ok10])
    (by decide +kernel)

theorem fam29_subs : ∀ k < fam29.subs.length, fam29.subOK k = true := by
  intro k hk
  have h : fam29.subs.length = 28 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam29_sub0_ok, fam29_sub1_ok, fam29_sub2_ok, fam29_sub3_ok, fam29_sub4_ok, fam29_sub5_ok, fam29_sub6_ok, fam29_sub7_ok, fam29_sub8_ok, fam29_sub9_ok, fam29_sub10_ok, fam29_sub11_ok, fam29_sub12_ok, fam29_sub13_ok, fam29_sub14_ok, fam29_sub15_ok, fam29_sub16_ok, fam29_sub17_ok, fam29_sub18_ok, fam29_sub19_ok, fam29_sub20_ok, fam29_sub21_ok, fam29_sub22_ok, fam29_sub23_ok, fam29_sub24_ok, fam29_sub25_ok, fam29_sub26_ok, fam29_sub27_ok]

end Kalai5.A16
