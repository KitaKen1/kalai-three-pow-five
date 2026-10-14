import Kalai5.A16.Data.Fam26
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 26. -/

namespace Kalai5.A16

theorem fam26_check : fam26.check = true := by decide +kernel

theorem fam26_recs_ok0 : fam26.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam26_recs_ok1 : fam26.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam26_recs_ok2 : fam26.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam26_recs_ok3 : fam26.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam26_recs_ok4 : fam26.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam26_recs_ok5 : fam26.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam26_recs_ok6 : fam26.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam26_recs_ok7 : fam26.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam26_recs_ok8 : fam26.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam26_recs_ok9 : fam26.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam26_recs_ok10 : fam26.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam26_recs_ok11 : fam26.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam26_sub0_ok : fam26.subOK 0 = true := by decide +kernel

theorem fam26_sub1_ok : fam26.subOK 1 = true := by decide +kernel

theorem fam26_sub2_ok : fam26.subOK 2 = true := by decide +kernel

theorem fam26_sub3_ok : fam26.subOK 3 = true := by decide +kernel

theorem fam26_sub4_ok : fam26.subOK 4 = true := by decide +kernel

theorem fam26_sub5_ok : fam26.subOK 5 = true := by decide +kernel

theorem fam26_sub6_ok : fam26.subOK 6 = true := by decide +kernel

theorem fam26_sub7_ok : fam26.subOK 7 = true := by decide +kernel

theorem fam26_sub8_ok : fam26.subOK 8 = true := by decide +kernel

theorem fam26_sub9_ok : fam26.subOK 9 = true := by decide +kernel

theorem fam26_sub10_ok : fam26.subOK 10 = true := by decide +kernel

theorem fam26_sub11_ok : fam26.subOK 11 = true := by decide +kernel

theorem fam26_sub12_ok : fam26.subOK 12 = true := by decide +kernel

theorem fam26_sub13_ok : fam26.subOK 13 = true := by decide +kernel

theorem fam26_sub14_ok : fam26.subOK 14 = true := by decide +kernel

theorem fam26_sub15_ok : fam26.subOK 15 = true := by decide +kernel

theorem fam26_sub16_ok : fam26.subOK 16 = true := by decide +kernel

theorem fam26_sub17_ok : fam26.subOK 17 = true := by decide +kernel

theorem fam26_sub18_ok : fam26.subOK 18 = true := by decide +kernel

theorem fam26_sub19_ok : fam26.subOK 19 = true := by decide +kernel

theorem fam26_sub20_ok : fam26.subOK 20 = true := by decide +kernel

theorem fam26_sub21_ok : fam26.subOK 21 = true := by decide +kernel

theorem fam26_sub22_ok : fam26.subOK 22 = true := by decide +kernel

theorem fam26_sub23_ok : fam26.subOK 23 = true := by decide +kernel

theorem fam26_sub24_ok : fam26.subOK 24 = true := by decide +kernel

theorem fam26_sub25_ok : fam26.subOK 25 = true := by decide +kernel

theorem fam26_sub26_ok : fam26.subOK 26 = true := by decide +kernel

theorem fam26_sub27_ok : fam26.subOK 27 = true := by decide +kernel

theorem fam26_sub28_ok : fam26.subOK 28 = true := by decide +kernel

theorem fam26_sub29_ok : fam26.subOK 29 = true := by decide +kernel

theorem fam26_sub30_ok : fam26.subOK 30 = true := by decide +kernel

theorem fam26_sub31_ok : fam26.subOK 31 = true := by decide +kernel

theorem fam26_sub32_ok : fam26.subOK 32 = true := by decide +kernel

theorem fam26_recs : ∀ r ∈ fam26.recs, fam26.recOK r = true :=
  fam26.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [fam26_recs_ok0, fam26_recs_ok1, fam26_recs_ok2, fam26_recs_ok3, fam26_recs_ok4, fam26_recs_ok5, fam26_recs_ok6, fam26_recs_ok7, fam26_recs_ok8, fam26_recs_ok9, fam26_recs_ok10, fam26_recs_ok11])
    (by decide +kernel)

theorem fam26_subs : ∀ k < fam26.subs.length, fam26.subOK k = true := by
  intro k hk
  have h : fam26.subs.length = 33 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam26_sub0_ok, fam26_sub1_ok, fam26_sub2_ok, fam26_sub3_ok, fam26_sub4_ok, fam26_sub5_ok, fam26_sub6_ok, fam26_sub7_ok, fam26_sub8_ok, fam26_sub9_ok, fam26_sub10_ok, fam26_sub11_ok, fam26_sub12_ok, fam26_sub13_ok, fam26_sub14_ok, fam26_sub15_ok, fam26_sub16_ok, fam26_sub17_ok, fam26_sub18_ok, fam26_sub19_ok, fam26_sub20_ok, fam26_sub21_ok, fam26_sub22_ok, fam26_sub23_ok, fam26_sub24_ok, fam26_sub25_ok, fam26_sub26_ok, fam26_sub27_ok, fam26_sub28_ok, fam26_sub29_ok, fam26_sub30_ok, fam26_sub31_ok, fam26_sub32_ok]

end Kalai5.A16
