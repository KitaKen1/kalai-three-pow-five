import Kalai5.A16.Data.Fam40
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 40. -/

namespace Kalai5.A16

theorem fam40_check : fam40.check = true := by decide +kernel

theorem fam40_recs_ok0 : fam40.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam40_recs_ok1 : fam40.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam40_recs_ok2 : fam40.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam40_recs_ok3 : fam40.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam40_recs_ok4 : fam40.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam40_recs_ok5 : fam40.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam40_recs_ok6 : fam40.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam40_recs_ok7 : fam40.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam40_recs_ok8 : fam40.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam40_recs_ok9 : fam40.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam40_recs_ok10 : fam40.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam40_recs_ok11 : fam40.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam40_recs_ok12 : fam40.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam40_recs_ok13 : fam40.recsOK (40 * 13) 40 = true := by decide +kernel

theorem fam40_sub0_ok : fam40.subOK 0 = true := by decide +kernel

theorem fam40_sub1_ok : fam40.subOK 1 = true := by decide +kernel

theorem fam40_sub2_ok : fam40.subOK 2 = true := by decide +kernel

theorem fam40_sub3_ok : fam40.subOK 3 = true := by decide +kernel

theorem fam40_sub4_ok : fam40.subOK 4 = true := by decide +kernel

theorem fam40_sub5_ok : fam40.subOK 5 = true := by decide +kernel

theorem fam40_sub6_ok : fam40.subOK 6 = true := by decide +kernel

theorem fam40_sub7_ok : fam40.subOK 7 = true := by decide +kernel

theorem fam40_sub8_ok : fam40.subOK 8 = true := by decide +kernel

theorem fam40_sub9_ok : fam40.subOK 9 = true := by decide +kernel

theorem fam40_sub10_ok : fam40.subOK 10 = true := by decide +kernel

theorem fam40_sub11_ok : fam40.subOK 11 = true := by decide +kernel

theorem fam40_sub12_ok : fam40.subOK 12 = true := by decide +kernel

theorem fam40_sub13_ok : fam40.subOK 13 = true := by decide +kernel

theorem fam40_sub14_ok : fam40.subOK 14 = true := by decide +kernel

theorem fam40_sub15_ok : fam40.subOK 15 = true := by decide +kernel

theorem fam40_sub16_ok : fam40.subOK 16 = true := by decide +kernel

theorem fam40_sub17_ok : fam40.subOK 17 = true := by decide +kernel

theorem fam40_sub18_ok : fam40.subOK 18 = true := by decide +kernel

theorem fam40_sub19_ok : fam40.subOK 19 = true := by decide +kernel

theorem fam40_sub20_ok : fam40.subOK 20 = true := by decide +kernel

theorem fam40_sub21_ok : fam40.subOK 21 = true := by decide +kernel

theorem fam40_sub22_ok : fam40.subOK 22 = true := by decide +kernel

theorem fam40_sub23_ok : fam40.subOK 23 = true := by decide +kernel

theorem fam40_sub24_ok : fam40.subOK 24 = true := by decide +kernel

theorem fam40_sub25_ok : fam40.subOK 25 = true := by decide +kernel

theorem fam40_sub26_ok : fam40.subOK 26 = true := by decide +kernel

theorem fam40_sub27_ok : fam40.subOK 27 = true := by decide +kernel

theorem fam40_sub28_ok : fam40.subOK 28 = true := by decide +kernel

theorem fam40_sub29_ok : fam40.subOK 29 = true := by decide +kernel

theorem fam40_sub30_ok : fam40.subOK 30 = true := by decide +kernel

theorem fam40_sub31_ok : fam40.subOK 31 = true := by decide +kernel

theorem fam40_sub32_ok : fam40.subOK 32 = true := by decide +kernel

theorem fam40_sub33_ok : fam40.subOK 33 = true := by decide +kernel

theorem fam40_sub34_ok : fam40.subOK 34 = true := by decide +kernel

theorem fam40_sub35_ok : fam40.subOK 35 = true := by decide +kernel

theorem fam40_sub36_ok : fam40.subOK 36 = true := by decide +kernel

theorem fam40_sub37_ok : fam40.subOK 37 = true := by decide +kernel

theorem fam40_recs : ∀ r ∈ fam40.recs, fam40.recOK r = true :=
  fam40.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [fam40_recs_ok0, fam40_recs_ok1, fam40_recs_ok2, fam40_recs_ok3, fam40_recs_ok4, fam40_recs_ok5, fam40_recs_ok6, fam40_recs_ok7, fam40_recs_ok8, fam40_recs_ok9, fam40_recs_ok10, fam40_recs_ok11, fam40_recs_ok12, fam40_recs_ok13])
    (by decide +kernel)

theorem fam40_subs : ∀ k < fam40.subs.length, fam40.subOK k = true := by
  intro k hk
  have h : fam40.subs.length = 38 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam40_sub0_ok, fam40_sub1_ok, fam40_sub2_ok, fam40_sub3_ok, fam40_sub4_ok, fam40_sub5_ok, fam40_sub6_ok, fam40_sub7_ok, fam40_sub8_ok, fam40_sub9_ok, fam40_sub10_ok, fam40_sub11_ok, fam40_sub12_ok, fam40_sub13_ok, fam40_sub14_ok, fam40_sub15_ok, fam40_sub16_ok, fam40_sub17_ok, fam40_sub18_ok, fam40_sub19_ok, fam40_sub20_ok, fam40_sub21_ok, fam40_sub22_ok, fam40_sub23_ok, fam40_sub24_ok, fam40_sub25_ok, fam40_sub26_ok, fam40_sub27_ok, fam40_sub28_ok, fam40_sub29_ok, fam40_sub30_ok, fam40_sub31_ok, fam40_sub32_ok, fam40_sub33_ok, fam40_sub34_ok, fam40_sub35_ok, fam40_sub36_ok, fam40_sub37_ok]

end Kalai5.A16
