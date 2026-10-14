import Kalai5.A16.Data.Fam54
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 54. -/

namespace Kalai5.A16

theorem fam54_check : fam54.check = true := by decide +kernel

theorem fam54_recs_ok0 : fam54.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam54_recs_ok1 : fam54.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam54_recs_ok2 : fam54.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam54_recs_ok3 : fam54.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam54_recs_ok4 : fam54.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam54_recs_ok5 : fam54.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam54_recs_ok6 : fam54.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam54_recs_ok7 : fam54.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam54_recs_ok8 : fam54.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam54_recs_ok9 : fam54.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam54_recs_ok10 : fam54.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam54_recs_ok11 : fam54.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam54_recs_ok12 : fam54.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam54_sub0_ok : fam54.subOK 0 = true := by decide +kernel

theorem fam54_sub1_ok : fam54.subOK 1 = true := by decide +kernel

theorem fam54_sub2_ok : fam54.subOK 2 = true := by decide +kernel

theorem fam54_sub3_ok : fam54.subOK 3 = true := by decide +kernel

theorem fam54_sub4_ok : fam54.subOK 4 = true := by decide +kernel

theorem fam54_sub5_ok : fam54.subOK 5 = true := by decide +kernel

theorem fam54_sub6_ok : fam54.subOK 6 = true := by decide +kernel

theorem fam54_sub7_ok : fam54.subOK 7 = true := by decide +kernel

theorem fam54_sub8_ok : fam54.subOK 8 = true := by decide +kernel

theorem fam54_sub9_ok : fam54.subOK 9 = true := by decide +kernel

theorem fam54_sub10_ok : fam54.subOK 10 = true := by decide +kernel

theorem fam54_sub11_ok : fam54.subOK 11 = true := by decide +kernel

theorem fam54_sub12_ok : fam54.subOK 12 = true := by decide +kernel

theorem fam54_sub13_ok : fam54.subOK 13 = true := by decide +kernel

theorem fam54_sub14_ok : fam54.subOK 14 = true := by decide +kernel

theorem fam54_sub15_ok : fam54.subOK 15 = true := by decide +kernel

theorem fam54_sub16_ok : fam54.subOK 16 = true := by decide +kernel

theorem fam54_sub17_ok : fam54.subOK 17 = true := by decide +kernel

theorem fam54_sub18_ok : fam54.subOK 18 = true := by decide +kernel

theorem fam54_sub19_ok : fam54.subOK 19 = true := by decide +kernel

theorem fam54_sub20_ok : fam54.subOK 20 = true := by decide +kernel

theorem fam54_sub21_ok : fam54.subOK 21 = true := by decide +kernel

theorem fam54_sub22_ok : fam54.subOK 22 = true := by decide +kernel

theorem fam54_sub23_ok : fam54.subOK 23 = true := by decide +kernel

theorem fam54_sub24_ok : fam54.subOK 24 = true := by decide +kernel

theorem fam54_sub25_ok : fam54.subOK 25 = true := by decide +kernel

theorem fam54_sub26_ok : fam54.subOK 26 = true := by decide +kernel

theorem fam54_sub27_ok : fam54.subOK 27 = true := by decide +kernel

theorem fam54_sub28_ok : fam54.subOK 28 = true := by decide +kernel

theorem fam54_sub29_ok : fam54.subOK 29 = true := by decide +kernel

theorem fam54_sub30_ok : fam54.subOK 30 = true := by decide +kernel

theorem fam54_sub31_ok : fam54.subOK 31 = true := by decide +kernel

theorem fam54_sub32_ok : fam54.subOK 32 = true := by decide +kernel

theorem fam54_sub33_ok : fam54.subOK 33 = true := by decide +kernel

theorem fam54_sub34_ok : fam54.subOK 34 = true := by decide +kernel

theorem fam54_sub35_ok : fam54.subOK 35 = true := by decide +kernel

theorem fam54_sub36_ok : fam54.subOK 36 = true := by decide +kernel

theorem fam54_sub37_ok : fam54.subOK 37 = true := by decide +kernel

theorem fam54_sub38_ok : fam54.subOK 38 = true := by decide +kernel

theorem fam54_sub39_ok : fam54.subOK 39 = true := by decide +kernel

theorem fam54_sub40_ok : fam54.subOK 40 = true := by decide +kernel

theorem fam54_sub41_ok : fam54.subOK 41 = true := by decide +kernel

theorem fam54_sub42_ok : fam54.subOK 42 = true := by decide +kernel

theorem fam54_sub43_ok : fam54.subOK 43 = true := by decide +kernel

theorem fam54_sub44_ok : fam54.subOK 44 = true := by decide +kernel

theorem fam54_sub45_ok : fam54.subOK 45 = true := by decide +kernel

theorem fam54_sub46_ok : fam54.subOK 46 = true := by decide +kernel

theorem fam54_sub47_ok : fam54.subOK 47 = true := by decide +kernel

theorem fam54_sub48_ok : fam54.subOK 48 = true := by decide +kernel

theorem fam54_sub49_ok : fam54.subOK 49 = true := by decide +kernel

theorem fam54_recs : ∀ r ∈ fam54.recs, fam54.recOK r = true :=
  fam54.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [fam54_recs_ok0, fam54_recs_ok1, fam54_recs_ok2, fam54_recs_ok3, fam54_recs_ok4, fam54_recs_ok5, fam54_recs_ok6, fam54_recs_ok7, fam54_recs_ok8, fam54_recs_ok9, fam54_recs_ok10, fam54_recs_ok11, fam54_recs_ok12])
    (by decide +kernel)

theorem fam54_subs : ∀ k < fam54.subs.length, fam54.subOK k = true := by
  intro k hk
  have h : fam54.subs.length = 50 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam54_sub0_ok, fam54_sub1_ok, fam54_sub2_ok, fam54_sub3_ok, fam54_sub4_ok, fam54_sub5_ok, fam54_sub6_ok, fam54_sub7_ok, fam54_sub8_ok, fam54_sub9_ok, fam54_sub10_ok, fam54_sub11_ok, fam54_sub12_ok, fam54_sub13_ok, fam54_sub14_ok, fam54_sub15_ok, fam54_sub16_ok, fam54_sub17_ok, fam54_sub18_ok, fam54_sub19_ok, fam54_sub20_ok, fam54_sub21_ok, fam54_sub22_ok, fam54_sub23_ok, fam54_sub24_ok, fam54_sub25_ok, fam54_sub26_ok, fam54_sub27_ok, fam54_sub28_ok, fam54_sub29_ok, fam54_sub30_ok, fam54_sub31_ok, fam54_sub32_ok, fam54_sub33_ok, fam54_sub34_ok, fam54_sub35_ok, fam54_sub36_ok, fam54_sub37_ok, fam54_sub38_ok, fam54_sub39_ok, fam54_sub40_ok, fam54_sub41_ok, fam54_sub42_ok, fam54_sub43_ok, fam54_sub44_ok, fam54_sub45_ok, fam54_sub46_ok, fam54_sub47_ok, fam54_sub48_ok, fam54_sub49_ok]

end Kalai5.A16
