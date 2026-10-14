import Kalai5.A16.Data.Fam9
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 9. -/

namespace Kalai5.A16

theorem fam9_check : fam9.check = true := by decide +kernel

theorem fam9_recs_ok0 : fam9.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam9_recs_ok1 : fam9.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam9_recs_ok2 : fam9.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam9_recs_ok3 : fam9.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam9_recs_ok4 : fam9.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam9_recs_ok5 : fam9.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam9_recs_ok6 : fam9.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam9_recs_ok7 : fam9.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam9_recs_ok8 : fam9.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam9_recs_ok9 : fam9.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam9_recs_ok10 : fam9.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam9_sub0_ok : fam9.subOK 0 = true := by decide +kernel

theorem fam9_sub1_ok : fam9.subOK 1 = true := by decide +kernel

theorem fam9_sub2_ok : fam9.subOK 2 = true := by decide +kernel

theorem fam9_sub3_ok : fam9.subOK 3 = true := by decide +kernel

theorem fam9_sub4_ok : fam9.subOK 4 = true := by decide +kernel

theorem fam9_sub5_ok : fam9.subOK 5 = true := by decide +kernel

theorem fam9_sub6_ok : fam9.subOK 6 = true := by decide +kernel

theorem fam9_sub7_ok : fam9.subOK 7 = true := by decide +kernel

theorem fam9_sub8_ok : fam9.subOK 8 = true := by decide +kernel

theorem fam9_sub9_ok : fam9.subOK 9 = true := by decide +kernel

theorem fam9_sub10_ok : fam9.subOK 10 = true := by decide +kernel

theorem fam9_sub11_ok : fam9.subOK 11 = true := by decide +kernel

theorem fam9_sub12_ok : fam9.subOK 12 = true := by decide +kernel

theorem fam9_sub13_ok : fam9.subOK 13 = true := by decide +kernel

theorem fam9_sub14_ok : fam9.subOK 14 = true := by decide +kernel

theorem fam9_sub15_ok : fam9.subOK 15 = true := by decide +kernel

theorem fam9_sub16_ok : fam9.subOK 16 = true := by decide +kernel

theorem fam9_sub17_ok : fam9.subOK 17 = true := by decide +kernel

theorem fam9_sub18_ok : fam9.subOK 18 = true := by decide +kernel

theorem fam9_sub19_ok : fam9.subOK 19 = true := by decide +kernel

theorem fam9_sub20_ok : fam9.subOK 20 = true := by decide +kernel

theorem fam9_sub21_ok : fam9.subOK 21 = true := by decide +kernel

theorem fam9_sub22_ok : fam9.subOK 22 = true := by decide +kernel

theorem fam9_sub23_ok : fam9.subOK 23 = true := by decide +kernel

theorem fam9_sub24_ok : fam9.subOK 24 = true := by decide +kernel

theorem fam9_sub25_ok : fam9.subOK 25 = true := by decide +kernel

theorem fam9_sub26_ok : fam9.subOK 26 = true := by decide +kernel

theorem fam9_sub27_ok : fam9.subOK 27 = true := by decide +kernel

theorem fam9_sub28_ok : fam9.subOK 28 = true := by decide +kernel

theorem fam9_sub29_ok : fam9.subOK 29 = true := by decide +kernel

theorem fam9_sub30_ok : fam9.subOK 30 = true := by decide +kernel

theorem fam9_sub31_ok : fam9.subOK 31 = true := by decide +kernel

theorem fam9_sub32_ok : fam9.subOK 32 = true := by decide +kernel

theorem fam9_recs : ∀ r ∈ fam9.recs, fam9.recOK r = true :=
  fam9.recs_of_chunks 11 (fun c hc => by
    interval_cases c
    exacts [fam9_recs_ok0, fam9_recs_ok1, fam9_recs_ok2, fam9_recs_ok3, fam9_recs_ok4, fam9_recs_ok5, fam9_recs_ok6, fam9_recs_ok7, fam9_recs_ok8, fam9_recs_ok9, fam9_recs_ok10])
    (by decide +kernel)

theorem fam9_subs : ∀ k < fam9.subs.length, fam9.subOK k = true := by
  intro k hk
  have h : fam9.subs.length = 33 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam9_sub0_ok, fam9_sub1_ok, fam9_sub2_ok, fam9_sub3_ok, fam9_sub4_ok, fam9_sub5_ok, fam9_sub6_ok, fam9_sub7_ok, fam9_sub8_ok, fam9_sub9_ok, fam9_sub10_ok, fam9_sub11_ok, fam9_sub12_ok, fam9_sub13_ok, fam9_sub14_ok, fam9_sub15_ok, fam9_sub16_ok, fam9_sub17_ok, fam9_sub18_ok, fam9_sub19_ok, fam9_sub20_ok, fam9_sub21_ok, fam9_sub22_ok, fam9_sub23_ok, fam9_sub24_ok, fam9_sub25_ok, fam9_sub26_ok, fam9_sub27_ok, fam9_sub28_ok, fam9_sub29_ok, fam9_sub30_ok, fam9_sub31_ok, fam9_sub32_ok]

end Kalai5.A16
