import Kalai5.A16.Data.Fam28
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 28. -/

namespace Kalai5.A16

theorem fam28_check : fam28.check = true := by decide +kernel

theorem fam28_recs_ok0 : fam28.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam28_recs_ok1 : fam28.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam28_recs_ok2 : fam28.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam28_recs_ok3 : fam28.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam28_recs_ok4 : fam28.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam28_recs_ok5 : fam28.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam28_recs_ok6 : fam28.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam28_recs_ok7 : fam28.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam28_recs_ok8 : fam28.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam28_recs_ok9 : fam28.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam28_recs_ok10 : fam28.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam28_sub0_ok : fam28.subOK 0 = true := by decide +kernel

theorem fam28_sub1_ok : fam28.subOK 1 = true := by decide +kernel

theorem fam28_sub2_ok : fam28.subOK 2 = true := by decide +kernel

theorem fam28_sub3_ok : fam28.subOK 3 = true := by decide +kernel

theorem fam28_sub4_ok : fam28.subOK 4 = true := by decide +kernel

theorem fam28_sub5_ok : fam28.subOK 5 = true := by decide +kernel

theorem fam28_sub6_ok : fam28.subOK 6 = true := by decide +kernel

theorem fam28_sub7_ok : fam28.subOK 7 = true := by decide +kernel

theorem fam28_sub8_ok : fam28.subOK 8 = true := by decide +kernel

theorem fam28_sub9_ok : fam28.subOK 9 = true := by decide +kernel

theorem fam28_sub10_ok : fam28.subOK 10 = true := by decide +kernel

theorem fam28_sub11_ok : fam28.subOK 11 = true := by decide +kernel

theorem fam28_sub12_ok : fam28.subOK 12 = true := by decide +kernel

theorem fam28_sub13_ok : fam28.subOK 13 = true := by decide +kernel

theorem fam28_sub14_ok : fam28.subOK 14 = true := by decide +kernel

theorem fam28_sub15_ok : fam28.subOK 15 = true := by decide +kernel

theorem fam28_sub16_ok : fam28.subOK 16 = true := by decide +kernel

theorem fam28_sub17_ok : fam28.subOK 17 = true := by decide +kernel

theorem fam28_sub18_ok : fam28.subOK 18 = true := by decide +kernel

theorem fam28_sub19_ok : fam28.subOK 19 = true := by decide +kernel

theorem fam28_sub20_ok : fam28.subOK 20 = true := by decide +kernel

theorem fam28_sub21_ok : fam28.subOK 21 = true := by decide +kernel

theorem fam28_sub22_ok : fam28.subOK 22 = true := by decide +kernel

theorem fam28_sub23_ok : fam28.subOK 23 = true := by decide +kernel

theorem fam28_sub24_ok : fam28.subOK 24 = true := by decide +kernel

theorem fam28_sub25_ok : fam28.subOK 25 = true := by decide +kernel

theorem fam28_sub26_ok : fam28.subOK 26 = true := by decide +kernel

theorem fam28_sub27_ok : fam28.subOK 27 = true := by decide +kernel

theorem fam28_sub28_ok : fam28.subOK 28 = true := by decide +kernel

theorem fam28_sub29_ok : fam28.subOK 29 = true := by decide +kernel

theorem fam28_sub30_ok : fam28.subOK 30 = true := by decide +kernel

theorem fam28_sub31_ok : fam28.subOK 31 = true := by decide +kernel

theorem fam28_sub32_ok : fam28.subOK 32 = true := by decide +kernel

theorem fam28_sub33_ok : fam28.subOK 33 = true := by decide +kernel

theorem fam28_recs : ∀ r ∈ fam28.recs, fam28.recOK r = true :=
  fam28.recs_of_chunks 11 (fun c hc => by
    interval_cases c
    exacts [fam28_recs_ok0, fam28_recs_ok1, fam28_recs_ok2, fam28_recs_ok3, fam28_recs_ok4, fam28_recs_ok5, fam28_recs_ok6, fam28_recs_ok7, fam28_recs_ok8, fam28_recs_ok9, fam28_recs_ok10])
    (by decide +kernel)

theorem fam28_subs : ∀ k < fam28.subs.length, fam28.subOK k = true := by
  intro k hk
  have h : fam28.subs.length = 34 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam28_sub0_ok, fam28_sub1_ok, fam28_sub2_ok, fam28_sub3_ok, fam28_sub4_ok, fam28_sub5_ok, fam28_sub6_ok, fam28_sub7_ok, fam28_sub8_ok, fam28_sub9_ok, fam28_sub10_ok, fam28_sub11_ok, fam28_sub12_ok, fam28_sub13_ok, fam28_sub14_ok, fam28_sub15_ok, fam28_sub16_ok, fam28_sub17_ok, fam28_sub18_ok, fam28_sub19_ok, fam28_sub20_ok, fam28_sub21_ok, fam28_sub22_ok, fam28_sub23_ok, fam28_sub24_ok, fam28_sub25_ok, fam28_sub26_ok, fam28_sub27_ok, fam28_sub28_ok, fam28_sub29_ok, fam28_sub30_ok, fam28_sub31_ok, fam28_sub32_ok, fam28_sub33_ok]

end Kalai5.A16
