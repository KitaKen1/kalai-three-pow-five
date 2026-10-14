import Kalai5.A16.Data.Fam36
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 36. -/

namespace Kalai5.A16

theorem fam36_check : fam36.check = true := by decide +kernel

theorem fam36_recs_ok0 : fam36.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam36_recs_ok1 : fam36.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam36_recs_ok2 : fam36.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam36_recs_ok3 : fam36.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam36_recs_ok4 : fam36.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam36_recs_ok5 : fam36.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam36_recs_ok6 : fam36.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam36_recs_ok7 : fam36.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam36_recs_ok8 : fam36.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam36_recs_ok9 : fam36.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam36_recs_ok10 : fam36.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam36_recs_ok11 : fam36.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam36_recs_ok12 : fam36.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam36_recs_ok13 : fam36.recsOK (40 * 13) 40 = true := by decide +kernel

theorem fam36_sub0_ok : fam36.subOK 0 = true := by decide +kernel

theorem fam36_sub1_ok : fam36.subOK 1 = true := by decide +kernel

theorem fam36_sub2_ok : fam36.subOK 2 = true := by decide +kernel

theorem fam36_sub3_ok : fam36.subOK 3 = true := by decide +kernel

theorem fam36_sub4_ok : fam36.subOK 4 = true := by decide +kernel

theorem fam36_sub5_ok : fam36.subOK 5 = true := by decide +kernel

theorem fam36_sub6_ok : fam36.subOK 6 = true := by decide +kernel

theorem fam36_sub7_ok : fam36.subOK 7 = true := by decide +kernel

theorem fam36_sub8_ok : fam36.subOK 8 = true := by decide +kernel

theorem fam36_sub9_ok : fam36.subOK 9 = true := by decide +kernel

theorem fam36_sub10_ok : fam36.subOK 10 = true := by decide +kernel

theorem fam36_sub11_ok : fam36.subOK 11 = true := by decide +kernel

theorem fam36_sub12_ok : fam36.subOK 12 = true := by decide +kernel

theorem fam36_sub13_ok : fam36.subOK 13 = true := by decide +kernel

theorem fam36_sub14_ok : fam36.subOK 14 = true := by decide +kernel

theorem fam36_sub15_ok : fam36.subOK 15 = true := by decide +kernel

theorem fam36_sub16_ok : fam36.subOK 16 = true := by decide +kernel

theorem fam36_sub17_ok : fam36.subOK 17 = true := by decide +kernel

theorem fam36_sub18_ok : fam36.subOK 18 = true := by decide +kernel

theorem fam36_sub19_ok : fam36.subOK 19 = true := by decide +kernel

theorem fam36_sub20_ok : fam36.subOK 20 = true := by decide +kernel

theorem fam36_sub21_ok : fam36.subOK 21 = true := by decide +kernel

theorem fam36_sub22_ok : fam36.subOK 22 = true := by decide +kernel

theorem fam36_sub23_ok : fam36.subOK 23 = true := by decide +kernel

theorem fam36_sub24_ok : fam36.subOK 24 = true := by decide +kernel

theorem fam36_sub25_ok : fam36.subOK 25 = true := by decide +kernel

theorem fam36_sub26_ok : fam36.subOK 26 = true := by decide +kernel

theorem fam36_sub27_ok : fam36.subOK 27 = true := by decide +kernel

theorem fam36_sub28_ok : fam36.subOK 28 = true := by decide +kernel

theorem fam36_sub29_ok : fam36.subOK 29 = true := by decide +kernel

theorem fam36_sub30_ok : fam36.subOK 30 = true := by decide +kernel

theorem fam36_sub31_ok : fam36.subOK 31 = true := by decide +kernel

theorem fam36_sub32_ok : fam36.subOK 32 = true := by decide +kernel

theorem fam36_sub33_ok : fam36.subOK 33 = true := by decide +kernel

theorem fam36_sub34_ok : fam36.subOK 34 = true := by decide +kernel

theorem fam36_sub35_ok : fam36.subOK 35 = true := by decide +kernel

theorem fam36_sub36_ok : fam36.subOK 36 = true := by decide +kernel

theorem fam36_sub37_ok : fam36.subOK 37 = true := by decide +kernel

theorem fam36_sub38_ok : fam36.subOK 38 = true := by decide +kernel

theorem fam36_sub39_ok : fam36.subOK 39 = true := by decide +kernel

theorem fam36_sub40_ok : fam36.subOK 40 = true := by decide +kernel

theorem fam36_sub41_ok : fam36.subOK 41 = true := by decide +kernel

theorem fam36_sub42_ok : fam36.subOK 42 = true := by decide +kernel

theorem fam36_sub43_ok : fam36.subOK 43 = true := by decide +kernel

theorem fam36_sub44_ok : fam36.subOK 44 = true := by decide +kernel

theorem fam36_sub45_ok : fam36.subOK 45 = true := by decide +kernel

theorem fam36_sub46_ok : fam36.subOK 46 = true := by decide +kernel

theorem fam36_recs : ∀ r ∈ fam36.recs, fam36.recOK r = true :=
  fam36.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [fam36_recs_ok0, fam36_recs_ok1, fam36_recs_ok2, fam36_recs_ok3, fam36_recs_ok4, fam36_recs_ok5, fam36_recs_ok6, fam36_recs_ok7, fam36_recs_ok8, fam36_recs_ok9, fam36_recs_ok10, fam36_recs_ok11, fam36_recs_ok12, fam36_recs_ok13])
    (by decide +kernel)

theorem fam36_subs : ∀ k < fam36.subs.length, fam36.subOK k = true := by
  intro k hk
  have h : fam36.subs.length = 47 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam36_sub0_ok, fam36_sub1_ok, fam36_sub2_ok, fam36_sub3_ok, fam36_sub4_ok, fam36_sub5_ok, fam36_sub6_ok, fam36_sub7_ok, fam36_sub8_ok, fam36_sub9_ok, fam36_sub10_ok, fam36_sub11_ok, fam36_sub12_ok, fam36_sub13_ok, fam36_sub14_ok, fam36_sub15_ok, fam36_sub16_ok, fam36_sub17_ok, fam36_sub18_ok, fam36_sub19_ok, fam36_sub20_ok, fam36_sub21_ok, fam36_sub22_ok, fam36_sub23_ok, fam36_sub24_ok, fam36_sub25_ok, fam36_sub26_ok, fam36_sub27_ok, fam36_sub28_ok, fam36_sub29_ok, fam36_sub30_ok, fam36_sub31_ok, fam36_sub32_ok, fam36_sub33_ok, fam36_sub34_ok, fam36_sub35_ok, fam36_sub36_ok, fam36_sub37_ok, fam36_sub38_ok, fam36_sub39_ok, fam36_sub40_ok, fam36_sub41_ok, fam36_sub42_ok, fam36_sub43_ok, fam36_sub44_ok, fam36_sub45_ok, fam36_sub46_ok]

end Kalai5.A16
