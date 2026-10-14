import Kalai5.A16.Data.Fam27
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 27. -/

namespace Kalai5.A16

theorem fam27_check : fam27.check = true := by decide +kernel

theorem fam27_recs_ok0 : fam27.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam27_recs_ok1 : fam27.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam27_recs_ok2 : fam27.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam27_recs_ok3 : fam27.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam27_recs_ok4 : fam27.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam27_recs_ok5 : fam27.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam27_recs_ok6 : fam27.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam27_recs_ok7 : fam27.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam27_recs_ok8 : fam27.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam27_recs_ok9 : fam27.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam27_recs_ok10 : fam27.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam27_recs_ok11 : fam27.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam27_recs_ok12 : fam27.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam27_sub0_ok : fam27.subOK 0 = true := by decide +kernel

theorem fam27_sub1_ok : fam27.subOK 1 = true := by decide +kernel

theorem fam27_sub2_ok : fam27.subOK 2 = true := by decide +kernel

theorem fam27_sub3_ok : fam27.subOK 3 = true := by decide +kernel

theorem fam27_sub4_ok : fam27.subOK 4 = true := by decide +kernel

theorem fam27_sub5_ok : fam27.subOK 5 = true := by decide +kernel

theorem fam27_sub6_ok : fam27.subOK 6 = true := by decide +kernel

theorem fam27_sub7_ok : fam27.subOK 7 = true := by decide +kernel

theorem fam27_sub8_ok : fam27.subOK 8 = true := by decide +kernel

theorem fam27_sub9_ok : fam27.subOK 9 = true := by decide +kernel

theorem fam27_sub10_ok : fam27.subOK 10 = true := by decide +kernel

theorem fam27_sub11_ok : fam27.subOK 11 = true := by decide +kernel

theorem fam27_sub12_ok : fam27.subOK 12 = true := by decide +kernel

theorem fam27_sub13_ok : fam27.subOK 13 = true := by decide +kernel

theorem fam27_sub14_ok : fam27.subOK 14 = true := by decide +kernel

theorem fam27_sub15_ok : fam27.subOK 15 = true := by decide +kernel

theorem fam27_sub16_ok : fam27.subOK 16 = true := by decide +kernel

theorem fam27_sub17_ok : fam27.subOK 17 = true := by decide +kernel

theorem fam27_sub18_ok : fam27.subOK 18 = true := by decide +kernel

theorem fam27_sub19_ok : fam27.subOK 19 = true := by decide +kernel

theorem fam27_sub20_ok : fam27.subOK 20 = true := by decide +kernel

theorem fam27_sub21_ok : fam27.subOK 21 = true := by decide +kernel

theorem fam27_sub22_ok : fam27.subOK 22 = true := by decide +kernel

theorem fam27_sub23_ok : fam27.subOK 23 = true := by decide +kernel

theorem fam27_sub24_ok : fam27.subOK 24 = true := by decide +kernel

theorem fam27_sub25_ok : fam27.subOK 25 = true := by decide +kernel

theorem fam27_sub26_ok : fam27.subOK 26 = true := by decide +kernel

theorem fam27_sub27_ok : fam27.subOK 27 = true := by decide +kernel

theorem fam27_sub28_ok : fam27.subOK 28 = true := by decide +kernel

theorem fam27_sub29_ok : fam27.subOK 29 = true := by decide +kernel

theorem fam27_sub30_ok : fam27.subOK 30 = true := by decide +kernel

theorem fam27_sub31_ok : fam27.subOK 31 = true := by decide +kernel

theorem fam27_sub32_ok : fam27.subOK 32 = true := by decide +kernel

theorem fam27_sub33_ok : fam27.subOK 33 = true := by decide +kernel

theorem fam27_sub34_ok : fam27.subOK 34 = true := by decide +kernel

theorem fam27_sub35_ok : fam27.subOK 35 = true := by decide +kernel

theorem fam27_sub36_ok : fam27.subOK 36 = true := by decide +kernel

theorem fam27_sub37_ok : fam27.subOK 37 = true := by decide +kernel

theorem fam27_sub38_ok : fam27.subOK 38 = true := by decide +kernel

theorem fam27_sub39_ok : fam27.subOK 39 = true := by decide +kernel

theorem fam27_sub40_ok : fam27.subOK 40 = true := by decide +kernel

theorem fam27_recs : ∀ r ∈ fam27.recs, fam27.recOK r = true :=
  fam27.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [fam27_recs_ok0, fam27_recs_ok1, fam27_recs_ok2, fam27_recs_ok3, fam27_recs_ok4, fam27_recs_ok5, fam27_recs_ok6, fam27_recs_ok7, fam27_recs_ok8, fam27_recs_ok9, fam27_recs_ok10, fam27_recs_ok11, fam27_recs_ok12])
    (by decide +kernel)

theorem fam27_subs : ∀ k < fam27.subs.length, fam27.subOK k = true := by
  intro k hk
  have h : fam27.subs.length = 41 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam27_sub0_ok, fam27_sub1_ok, fam27_sub2_ok, fam27_sub3_ok, fam27_sub4_ok, fam27_sub5_ok, fam27_sub6_ok, fam27_sub7_ok, fam27_sub8_ok, fam27_sub9_ok, fam27_sub10_ok, fam27_sub11_ok, fam27_sub12_ok, fam27_sub13_ok, fam27_sub14_ok, fam27_sub15_ok, fam27_sub16_ok, fam27_sub17_ok, fam27_sub18_ok, fam27_sub19_ok, fam27_sub20_ok, fam27_sub21_ok, fam27_sub22_ok, fam27_sub23_ok, fam27_sub24_ok, fam27_sub25_ok, fam27_sub26_ok, fam27_sub27_ok, fam27_sub28_ok, fam27_sub29_ok, fam27_sub30_ok, fam27_sub31_ok, fam27_sub32_ok, fam27_sub33_ok, fam27_sub34_ok, fam27_sub35_ok, fam27_sub36_ok, fam27_sub37_ok, fam27_sub38_ok, fam27_sub39_ok, fam27_sub40_ok]

end Kalai5.A16
