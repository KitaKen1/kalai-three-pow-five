import Kalai5.A16.Data.Fam25
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 25. -/

namespace Kalai5.A16

theorem fam25_check : fam25.check = true := by decide +kernel

theorem fam25_recs_ok0 : fam25.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam25_recs_ok1 : fam25.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam25_recs_ok2 : fam25.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam25_recs_ok3 : fam25.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam25_recs_ok4 : fam25.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam25_recs_ok5 : fam25.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam25_recs_ok6 : fam25.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam25_recs_ok7 : fam25.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam25_recs_ok8 : fam25.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam25_recs_ok9 : fam25.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam25_recs_ok10 : fam25.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam25_recs_ok11 : fam25.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam25_recs_ok12 : fam25.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam25_recs_ok13 : fam25.recsOK (40 * 13) 40 = true := by decide +kernel

theorem fam25_sub0_ok : fam25.subOK 0 = true := by decide +kernel

theorem fam25_sub1_ok : fam25.subOK 1 = true := by decide +kernel

theorem fam25_sub2_ok : fam25.subOK 2 = true := by decide +kernel

theorem fam25_sub3_ok : fam25.subOK 3 = true := by decide +kernel

theorem fam25_sub4_ok : fam25.subOK 4 = true := by decide +kernel

theorem fam25_sub5_ok : fam25.subOK 5 = true := by decide +kernel

theorem fam25_sub6_ok : fam25.subOK 6 = true := by decide +kernel

theorem fam25_sub7_ok : fam25.subOK 7 = true := by decide +kernel

theorem fam25_sub8_ok : fam25.subOK 8 = true := by decide +kernel

theorem fam25_sub9_ok : fam25.subOK 9 = true := by decide +kernel

theorem fam25_sub10_ok : fam25.subOK 10 = true := by decide +kernel

theorem fam25_sub11_ok : fam25.subOK 11 = true := by decide +kernel

theorem fam25_sub12_ok : fam25.subOK 12 = true := by decide +kernel

theorem fam25_sub13_ok : fam25.subOK 13 = true := by decide +kernel

theorem fam25_sub14_ok : fam25.subOK 14 = true := by decide +kernel

theorem fam25_sub15_ok : fam25.subOK 15 = true := by decide +kernel

theorem fam25_sub16_ok : fam25.subOK 16 = true := by decide +kernel

theorem fam25_sub17_ok : fam25.subOK 17 = true := by decide +kernel

theorem fam25_sub18_ok : fam25.subOK 18 = true := by decide +kernel

theorem fam25_sub19_ok : fam25.subOK 19 = true := by decide +kernel

theorem fam25_sub20_ok : fam25.subOK 20 = true := by decide +kernel

theorem fam25_sub21_ok : fam25.subOK 21 = true := by decide +kernel

theorem fam25_sub22_ok : fam25.subOK 22 = true := by decide +kernel

theorem fam25_sub23_ok : fam25.subOK 23 = true := by decide +kernel

theorem fam25_sub24_ok : fam25.subOK 24 = true := by decide +kernel

theorem fam25_sub25_ok : fam25.subOK 25 = true := by decide +kernel

theorem fam25_sub26_ok : fam25.subOK 26 = true := by decide +kernel

theorem fam25_sub27_ok : fam25.subOK 27 = true := by decide +kernel

theorem fam25_sub28_ok : fam25.subOK 28 = true := by decide +kernel

theorem fam25_sub29_ok : fam25.subOK 29 = true := by decide +kernel

theorem fam25_sub30_ok : fam25.subOK 30 = true := by decide +kernel

theorem fam25_sub31_ok : fam25.subOK 31 = true := by decide +kernel

theorem fam25_sub32_ok : fam25.subOK 32 = true := by decide +kernel

theorem fam25_sub33_ok : fam25.subOK 33 = true := by decide +kernel

theorem fam25_sub34_ok : fam25.subOK 34 = true := by decide +kernel

theorem fam25_sub35_ok : fam25.subOK 35 = true := by decide +kernel

theorem fam25_sub36_ok : fam25.subOK 36 = true := by decide +kernel

theorem fam25_sub37_ok : fam25.subOK 37 = true := by decide +kernel

theorem fam25_sub38_ok : fam25.subOK 38 = true := by decide +kernel

theorem fam25_sub39_ok : fam25.subOK 39 = true := by decide +kernel

theorem fam25_sub40_ok : fam25.subOK 40 = true := by decide +kernel

theorem fam25_sub41_ok : fam25.subOK 41 = true := by decide +kernel

theorem fam25_sub42_ok : fam25.subOK 42 = true := by decide +kernel

theorem fam25_sub43_ok : fam25.subOK 43 = true := by decide +kernel

theorem fam25_sub44_ok : fam25.subOK 44 = true := by decide +kernel

theorem fam25_sub45_ok : fam25.subOK 45 = true := by decide +kernel

theorem fam25_recs : ∀ r ∈ fam25.recs, fam25.recOK r = true :=
  fam25.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [fam25_recs_ok0, fam25_recs_ok1, fam25_recs_ok2, fam25_recs_ok3, fam25_recs_ok4, fam25_recs_ok5, fam25_recs_ok6, fam25_recs_ok7, fam25_recs_ok8, fam25_recs_ok9, fam25_recs_ok10, fam25_recs_ok11, fam25_recs_ok12, fam25_recs_ok13])
    (by decide +kernel)

theorem fam25_subs : ∀ k < fam25.subs.length, fam25.subOK k = true := by
  intro k hk
  have h : fam25.subs.length = 46 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam25_sub0_ok, fam25_sub1_ok, fam25_sub2_ok, fam25_sub3_ok, fam25_sub4_ok, fam25_sub5_ok, fam25_sub6_ok, fam25_sub7_ok, fam25_sub8_ok, fam25_sub9_ok, fam25_sub10_ok, fam25_sub11_ok, fam25_sub12_ok, fam25_sub13_ok, fam25_sub14_ok, fam25_sub15_ok, fam25_sub16_ok, fam25_sub17_ok, fam25_sub18_ok, fam25_sub19_ok, fam25_sub20_ok, fam25_sub21_ok, fam25_sub22_ok, fam25_sub23_ok, fam25_sub24_ok, fam25_sub25_ok, fam25_sub26_ok, fam25_sub27_ok, fam25_sub28_ok, fam25_sub29_ok, fam25_sub30_ok, fam25_sub31_ok, fam25_sub32_ok, fam25_sub33_ok, fam25_sub34_ok, fam25_sub35_ok, fam25_sub36_ok, fam25_sub37_ok, fam25_sub38_ok, fam25_sub39_ok, fam25_sub40_ok, fam25_sub41_ok, fam25_sub42_ok, fam25_sub43_ok, fam25_sub44_ok, fam25_sub45_ok]

end Kalai5.A16
