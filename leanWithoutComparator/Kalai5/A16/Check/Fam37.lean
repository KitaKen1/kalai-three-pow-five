import Kalai5.A16.Data.Fam37
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 37. -/

namespace Kalai5.A16

theorem fam37_check : fam37.check = true := by decide +kernel

theorem fam37_recs_ok0 : fam37.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam37_recs_ok1 : fam37.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam37_recs_ok2 : fam37.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam37_recs_ok3 : fam37.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam37_recs_ok4 : fam37.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam37_recs_ok5 : fam37.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam37_recs_ok6 : fam37.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam37_recs_ok7 : fam37.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam37_recs_ok8 : fam37.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam37_recs_ok9 : fam37.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam37_recs_ok10 : fam37.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam37_recs_ok11 : fam37.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam37_recs_ok12 : fam37.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam37_recs_ok13 : fam37.recsOK (40 * 13) 40 = true := by decide +kernel

theorem fam37_recs_ok14 : fam37.recsOK (40 * 14) 40 = true := by decide +kernel

theorem fam37_sub0_ok : fam37.subOK 0 = true := by decide +kernel

theorem fam37_sub1_ok : fam37.subOK 1 = true := by decide +kernel

theorem fam37_sub2_ok : fam37.subOK 2 = true := by decide +kernel

theorem fam37_sub3_ok : fam37.subOK 3 = true := by decide +kernel

theorem fam37_sub4_ok : fam37.subOK 4 = true := by decide +kernel

theorem fam37_sub5_ok : fam37.subOK 5 = true := by decide +kernel

theorem fam37_sub6_ok : fam37.subOK 6 = true := by decide +kernel

theorem fam37_sub7_ok : fam37.subOK 7 = true := by decide +kernel

theorem fam37_sub8_ok : fam37.subOK 8 = true := by decide +kernel

theorem fam37_sub9_ok : fam37.subOK 9 = true := by decide +kernel

theorem fam37_sub10_ok : fam37.subOK 10 = true := by decide +kernel

theorem fam37_sub11_ok : fam37.subOK 11 = true := by decide +kernel

theorem fam37_sub12_ok : fam37.subOK 12 = true := by decide +kernel

theorem fam37_sub13_ok : fam37.subOK 13 = true := by decide +kernel

theorem fam37_sub14_ok : fam37.subOK 14 = true := by decide +kernel

theorem fam37_sub15_ok : fam37.subOK 15 = true := by decide +kernel

theorem fam37_sub16_ok : fam37.subOK 16 = true := by decide +kernel

theorem fam37_sub17_ok : fam37.subOK 17 = true := by decide +kernel

theorem fam37_sub18_ok : fam37.subOK 18 = true := by decide +kernel

theorem fam37_sub19_ok : fam37.subOK 19 = true := by decide +kernel

theorem fam37_sub20_ok : fam37.subOK 20 = true := by decide +kernel

theorem fam37_sub21_ok : fam37.subOK 21 = true := by decide +kernel

theorem fam37_sub22_ok : fam37.subOK 22 = true := by decide +kernel

theorem fam37_sub23_ok : fam37.subOK 23 = true := by decide +kernel

theorem fam37_sub24_ok : fam37.subOK 24 = true := by decide +kernel

theorem fam37_sub25_ok : fam37.subOK 25 = true := by decide +kernel

theorem fam37_sub26_ok : fam37.subOK 26 = true := by decide +kernel

theorem fam37_sub27_ok : fam37.subOK 27 = true := by decide +kernel

theorem fam37_sub28_ok : fam37.subOK 28 = true := by decide +kernel

theorem fam37_sub29_ok : fam37.subOK 29 = true := by decide +kernel

theorem fam37_sub30_ok : fam37.subOK 30 = true := by decide +kernel

theorem fam37_sub31_ok : fam37.subOK 31 = true := by decide +kernel

theorem fam37_sub32_ok : fam37.subOK 32 = true := by decide +kernel

theorem fam37_sub33_ok : fam37.subOK 33 = true := by decide +kernel

theorem fam37_sub34_ok : fam37.subOK 34 = true := by decide +kernel

theorem fam37_sub35_ok : fam37.subOK 35 = true := by decide +kernel

theorem fam37_sub36_ok : fam37.subOK 36 = true := by decide +kernel

theorem fam37_sub37_ok : fam37.subOK 37 = true := by decide +kernel

theorem fam37_sub38_ok : fam37.subOK 38 = true := by decide +kernel

theorem fam37_sub39_ok : fam37.subOK 39 = true := by decide +kernel

theorem fam37_sub40_ok : fam37.subOK 40 = true := by decide +kernel

theorem fam37_sub41_ok : fam37.subOK 41 = true := by decide +kernel

theorem fam37_sub42_ok : fam37.subOK 42 = true := by decide +kernel

theorem fam37_sub43_ok : fam37.subOK 43 = true := by decide +kernel

theorem fam37_sub44_ok : fam37.subOK 44 = true := by decide +kernel

theorem fam37_sub45_ok : fam37.subOK 45 = true := by decide +kernel

theorem fam37_sub46_ok : fam37.subOK 46 = true := by decide +kernel

theorem fam37_recs : ∀ r ∈ fam37.recs, fam37.recOK r = true :=
  fam37.recs_of_chunks 15 (fun c hc => by
    interval_cases c
    exacts [fam37_recs_ok0, fam37_recs_ok1, fam37_recs_ok2, fam37_recs_ok3, fam37_recs_ok4, fam37_recs_ok5, fam37_recs_ok6, fam37_recs_ok7, fam37_recs_ok8, fam37_recs_ok9, fam37_recs_ok10, fam37_recs_ok11, fam37_recs_ok12, fam37_recs_ok13, fam37_recs_ok14])
    (by decide +kernel)

theorem fam37_subs : ∀ k < fam37.subs.length, fam37.subOK k = true := by
  intro k hk
  have h : fam37.subs.length = 47 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam37_sub0_ok, fam37_sub1_ok, fam37_sub2_ok, fam37_sub3_ok, fam37_sub4_ok, fam37_sub5_ok, fam37_sub6_ok, fam37_sub7_ok, fam37_sub8_ok, fam37_sub9_ok, fam37_sub10_ok, fam37_sub11_ok, fam37_sub12_ok, fam37_sub13_ok, fam37_sub14_ok, fam37_sub15_ok, fam37_sub16_ok, fam37_sub17_ok, fam37_sub18_ok, fam37_sub19_ok, fam37_sub20_ok, fam37_sub21_ok, fam37_sub22_ok, fam37_sub23_ok, fam37_sub24_ok, fam37_sub25_ok, fam37_sub26_ok, fam37_sub27_ok, fam37_sub28_ok, fam37_sub29_ok, fam37_sub30_ok, fam37_sub31_ok, fam37_sub32_ok, fam37_sub33_ok, fam37_sub34_ok, fam37_sub35_ok, fam37_sub36_ok, fam37_sub37_ok, fam37_sub38_ok, fam37_sub39_ok, fam37_sub40_ok, fam37_sub41_ok, fam37_sub42_ok, fam37_sub43_ok, fam37_sub44_ok, fam37_sub45_ok, fam37_sub46_ok]

end Kalai5.A16
