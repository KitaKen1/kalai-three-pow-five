import Kalai5.A16.Data.Fam24
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 24. -/

namespace Kalai5.A16

theorem fam24_check : fam24.check = true := by decide +kernel

theorem fam24_recs_ok0 : fam24.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam24_recs_ok1 : fam24.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam24_recs_ok2 : fam24.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam24_recs_ok3 : fam24.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam24_recs_ok4 : fam24.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam24_recs_ok5 : fam24.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam24_recs_ok6 : fam24.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam24_recs_ok7 : fam24.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam24_recs_ok8 : fam24.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam24_recs_ok9 : fam24.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam24_recs_ok10 : fam24.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam24_recs_ok11 : fam24.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam24_sub0_ok : fam24.subOK 0 = true := by decide +kernel

theorem fam24_sub1_ok : fam24.subOK 1 = true := by decide +kernel

theorem fam24_sub2_ok : fam24.subOK 2 = true := by decide +kernel

theorem fam24_sub3_ok : fam24.subOK 3 = true := by decide +kernel

theorem fam24_sub4_ok : fam24.subOK 4 = true := by decide +kernel

theorem fam24_sub5_ok : fam24.subOK 5 = true := by decide +kernel

theorem fam24_sub6_ok : fam24.subOK 6 = true := by decide +kernel

theorem fam24_sub7_ok : fam24.subOK 7 = true := by decide +kernel

theorem fam24_sub8_ok : fam24.subOK 8 = true := by decide +kernel

theorem fam24_sub9_ok : fam24.subOK 9 = true := by decide +kernel

theorem fam24_sub10_ok : fam24.subOK 10 = true := by decide +kernel

theorem fam24_sub11_ok : fam24.subOK 11 = true := by decide +kernel

theorem fam24_sub12_ok : fam24.subOK 12 = true := by decide +kernel

theorem fam24_sub13_ok : fam24.subOK 13 = true := by decide +kernel

theorem fam24_sub14_ok : fam24.subOK 14 = true := by decide +kernel

theorem fam24_sub15_ok : fam24.subOK 15 = true := by decide +kernel

theorem fam24_sub16_ok : fam24.subOK 16 = true := by decide +kernel

theorem fam24_sub17_ok : fam24.subOK 17 = true := by decide +kernel

theorem fam24_sub18_ok : fam24.subOK 18 = true := by decide +kernel

theorem fam24_sub19_ok : fam24.subOK 19 = true := by decide +kernel

theorem fam24_sub20_ok : fam24.subOK 20 = true := by decide +kernel

theorem fam24_sub21_ok : fam24.subOK 21 = true := by decide +kernel

theorem fam24_sub22_ok : fam24.subOK 22 = true := by decide +kernel

theorem fam24_sub23_ok : fam24.subOK 23 = true := by decide +kernel

theorem fam24_sub24_ok : fam24.subOK 24 = true := by decide +kernel

theorem fam24_sub25_ok : fam24.subOK 25 = true := by decide +kernel

theorem fam24_sub26_ok : fam24.subOK 26 = true := by decide +kernel

theorem fam24_sub27_ok : fam24.subOK 27 = true := by decide +kernel

theorem fam24_sub28_ok : fam24.subOK 28 = true := by decide +kernel

theorem fam24_sub29_ok : fam24.subOK 29 = true := by decide +kernel

theorem fam24_sub30_ok : fam24.subOK 30 = true := by decide +kernel

theorem fam24_sub31_ok : fam24.subOK 31 = true := by decide +kernel

theorem fam24_sub32_ok : fam24.subOK 32 = true := by decide +kernel

theorem fam24_sub33_ok : fam24.subOK 33 = true := by decide +kernel

theorem fam24_sub34_ok : fam24.subOK 34 = true := by decide +kernel

theorem fam24_recs : ∀ r ∈ fam24.recs, fam24.recOK r = true :=
  fam24.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [fam24_recs_ok0, fam24_recs_ok1, fam24_recs_ok2, fam24_recs_ok3, fam24_recs_ok4, fam24_recs_ok5, fam24_recs_ok6, fam24_recs_ok7, fam24_recs_ok8, fam24_recs_ok9, fam24_recs_ok10, fam24_recs_ok11])
    (by decide +kernel)

theorem fam24_subs : ∀ k < fam24.subs.length, fam24.subOK k = true := by
  intro k hk
  have h : fam24.subs.length = 35 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam24_sub0_ok, fam24_sub1_ok, fam24_sub2_ok, fam24_sub3_ok, fam24_sub4_ok, fam24_sub5_ok, fam24_sub6_ok, fam24_sub7_ok, fam24_sub8_ok, fam24_sub9_ok, fam24_sub10_ok, fam24_sub11_ok, fam24_sub12_ok, fam24_sub13_ok, fam24_sub14_ok, fam24_sub15_ok, fam24_sub16_ok, fam24_sub17_ok, fam24_sub18_ok, fam24_sub19_ok, fam24_sub20_ok, fam24_sub21_ok, fam24_sub22_ok, fam24_sub23_ok, fam24_sub24_ok, fam24_sub25_ok, fam24_sub26_ok, fam24_sub27_ok, fam24_sub28_ok, fam24_sub29_ok, fam24_sub30_ok, fam24_sub31_ok, fam24_sub32_ok, fam24_sub33_ok, fam24_sub34_ok]

end Kalai5.A16
