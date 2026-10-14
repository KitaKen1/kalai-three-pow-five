import Kalai5.A16.Data.Fam15
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 15. -/

namespace Kalai5.A16

theorem fam15_check : fam15.check = true := by decide +kernel

theorem fam15_recs_ok0 : fam15.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam15_recs_ok1 : fam15.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam15_recs_ok2 : fam15.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam15_recs_ok3 : fam15.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam15_recs_ok4 : fam15.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam15_recs_ok5 : fam15.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam15_recs_ok6 : fam15.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam15_recs_ok7 : fam15.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam15_recs_ok8 : fam15.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam15_recs_ok9 : fam15.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam15_recs_ok10 : fam15.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam15_recs_ok11 : fam15.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam15_recs_ok12 : fam15.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam15_recs_ok13 : fam15.recsOK (40 * 13) 40 = true := by decide +kernel

theorem fam15_sub0_ok : fam15.subOK 0 = true := by decide +kernel

theorem fam15_sub1_ok : fam15.subOK 1 = true := by decide +kernel

theorem fam15_sub2_ok : fam15.subOK 2 = true := by decide +kernel

theorem fam15_sub3_ok : fam15.subOK 3 = true := by decide +kernel

theorem fam15_sub4_ok : fam15.subOK 4 = true := by decide +kernel

theorem fam15_sub5_ok : fam15.subOK 5 = true := by decide +kernel

theorem fam15_sub6_ok : fam15.subOK 6 = true := by decide +kernel

theorem fam15_sub7_ok : fam15.subOK 7 = true := by decide +kernel

theorem fam15_sub8_ok : fam15.subOK 8 = true := by decide +kernel

theorem fam15_sub9_ok : fam15.subOK 9 = true := by decide +kernel

theorem fam15_sub10_ok : fam15.subOK 10 = true := by decide +kernel

theorem fam15_sub11_ok : fam15.subOK 11 = true := by decide +kernel

theorem fam15_sub12_ok : fam15.subOK 12 = true := by decide +kernel

theorem fam15_sub13_ok : fam15.subOK 13 = true := by decide +kernel

theorem fam15_sub14_ok : fam15.subOK 14 = true := by decide +kernel

theorem fam15_sub15_ok : fam15.subOK 15 = true := by decide +kernel

theorem fam15_sub16_ok : fam15.subOK 16 = true := by decide +kernel

theorem fam15_sub17_ok : fam15.subOK 17 = true := by decide +kernel

theorem fam15_sub18_ok : fam15.subOK 18 = true := by decide +kernel

theorem fam15_sub19_ok : fam15.subOK 19 = true := by decide +kernel

theorem fam15_sub20_ok : fam15.subOK 20 = true := by decide +kernel

theorem fam15_sub21_ok : fam15.subOK 21 = true := by decide +kernel

theorem fam15_sub22_ok : fam15.subOK 22 = true := by decide +kernel

theorem fam15_sub23_ok : fam15.subOK 23 = true := by decide +kernel

theorem fam15_sub24_ok : fam15.subOK 24 = true := by decide +kernel

theorem fam15_sub25_ok : fam15.subOK 25 = true := by decide +kernel

theorem fam15_sub26_ok : fam15.subOK 26 = true := by decide +kernel

theorem fam15_sub27_ok : fam15.subOK 27 = true := by decide +kernel

theorem fam15_sub28_ok : fam15.subOK 28 = true := by decide +kernel

theorem fam15_sub29_ok : fam15.subOK 29 = true := by decide +kernel

theorem fam15_sub30_ok : fam15.subOK 30 = true := by decide +kernel

theorem fam15_sub31_ok : fam15.subOK 31 = true := by decide +kernel

theorem fam15_sub32_ok : fam15.subOK 32 = true := by decide +kernel

theorem fam15_sub33_ok : fam15.subOK 33 = true := by decide +kernel

theorem fam15_sub34_ok : fam15.subOK 34 = true := by decide +kernel

theorem fam15_sub35_ok : fam15.subOK 35 = true := by decide +kernel

theorem fam15_sub36_ok : fam15.subOK 36 = true := by decide +kernel

theorem fam15_sub37_ok : fam15.subOK 37 = true := by decide +kernel

theorem fam15_sub38_ok : fam15.subOK 38 = true := by decide +kernel

theorem fam15_sub39_ok : fam15.subOK 39 = true := by decide +kernel

theorem fam15_sub40_ok : fam15.subOK 40 = true := by decide +kernel

theorem fam15_sub41_ok : fam15.subOK 41 = true := by decide +kernel

theorem fam15_sub42_ok : fam15.subOK 42 = true := by decide +kernel

theorem fam15_sub43_ok : fam15.subOK 43 = true := by decide +kernel

theorem fam15_sub44_ok : fam15.subOK 44 = true := by decide +kernel

theorem fam15_sub45_ok : fam15.subOK 45 = true := by decide +kernel

theorem fam15_sub46_ok : fam15.subOK 46 = true := by decide +kernel

theorem fam15_sub47_ok : fam15.subOK 47 = true := by decide +kernel

theorem fam15_sub48_ok : fam15.subOK 48 = true := by decide +kernel

theorem fam15_recs : ∀ r ∈ fam15.recs, fam15.recOK r = true :=
  fam15.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [fam15_recs_ok0, fam15_recs_ok1, fam15_recs_ok2, fam15_recs_ok3, fam15_recs_ok4, fam15_recs_ok5, fam15_recs_ok6, fam15_recs_ok7, fam15_recs_ok8, fam15_recs_ok9, fam15_recs_ok10, fam15_recs_ok11, fam15_recs_ok12, fam15_recs_ok13])
    (by decide +kernel)

theorem fam15_subs : ∀ k < fam15.subs.length, fam15.subOK k = true := by
  intro k hk
  have h : fam15.subs.length = 49 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam15_sub0_ok, fam15_sub1_ok, fam15_sub2_ok, fam15_sub3_ok, fam15_sub4_ok, fam15_sub5_ok, fam15_sub6_ok, fam15_sub7_ok, fam15_sub8_ok, fam15_sub9_ok, fam15_sub10_ok, fam15_sub11_ok, fam15_sub12_ok, fam15_sub13_ok, fam15_sub14_ok, fam15_sub15_ok, fam15_sub16_ok, fam15_sub17_ok, fam15_sub18_ok, fam15_sub19_ok, fam15_sub20_ok, fam15_sub21_ok, fam15_sub22_ok, fam15_sub23_ok, fam15_sub24_ok, fam15_sub25_ok, fam15_sub26_ok, fam15_sub27_ok, fam15_sub28_ok, fam15_sub29_ok, fam15_sub30_ok, fam15_sub31_ok, fam15_sub32_ok, fam15_sub33_ok, fam15_sub34_ok, fam15_sub35_ok, fam15_sub36_ok, fam15_sub37_ok, fam15_sub38_ok, fam15_sub39_ok, fam15_sub40_ok, fam15_sub41_ok, fam15_sub42_ok, fam15_sub43_ok, fam15_sub44_ok, fam15_sub45_ok, fam15_sub46_ok, fam15_sub47_ok, fam15_sub48_ok]

end Kalai5.A16
