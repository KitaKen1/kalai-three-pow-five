import Kalai5.A16.Data.Fam57
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 57. -/

namespace Kalai5.A16

theorem fam57_check : fam57.check = true := by decide +kernel

theorem fam57_recs_ok0 : fam57.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam57_recs_ok1 : fam57.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam57_recs_ok2 : fam57.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam57_recs_ok3 : fam57.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam57_recs_ok4 : fam57.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam57_recs_ok5 : fam57.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam57_recs_ok6 : fam57.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam57_recs_ok7 : fam57.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam57_recs_ok8 : fam57.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam57_recs_ok9 : fam57.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam57_recs_ok10 : fam57.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam57_recs_ok11 : fam57.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam57_recs_ok12 : fam57.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam57_sub0_ok : fam57.subOK 0 = true := by decide +kernel

theorem fam57_sub1_ok : fam57.subOK 1 = true := by decide +kernel

theorem fam57_sub2_ok : fam57.subOK 2 = true := by decide +kernel

theorem fam57_sub3_ok : fam57.subOK 3 = true := by decide +kernel

theorem fam57_sub4_ok : fam57.subOK 4 = true := by decide +kernel

theorem fam57_sub5_ok : fam57.subOK 5 = true := by decide +kernel

theorem fam57_sub6_ok : fam57.subOK 6 = true := by decide +kernel

theorem fam57_sub7_ok : fam57.subOK 7 = true := by decide +kernel

theorem fam57_sub8_ok : fam57.subOK 8 = true := by decide +kernel

theorem fam57_sub9_ok : fam57.subOK 9 = true := by decide +kernel

theorem fam57_sub10_ok : fam57.subOK 10 = true := by decide +kernel

theorem fam57_sub11_ok : fam57.subOK 11 = true := by decide +kernel

theorem fam57_sub12_ok : fam57.subOK 12 = true := by decide +kernel

theorem fam57_sub13_ok : fam57.subOK 13 = true := by decide +kernel

theorem fam57_sub14_ok : fam57.subOK 14 = true := by decide +kernel

theorem fam57_sub15_ok : fam57.subOK 15 = true := by decide +kernel

theorem fam57_sub16_ok : fam57.subOK 16 = true := by decide +kernel

theorem fam57_sub17_ok : fam57.subOK 17 = true := by decide +kernel

theorem fam57_sub18_ok : fam57.subOK 18 = true := by decide +kernel

theorem fam57_sub19_ok : fam57.subOK 19 = true := by decide +kernel

theorem fam57_sub20_ok : fam57.subOK 20 = true := by decide +kernel

theorem fam57_sub21_ok : fam57.subOK 21 = true := by decide +kernel

theorem fam57_sub22_ok : fam57.subOK 22 = true := by decide +kernel

theorem fam57_sub23_ok : fam57.subOK 23 = true := by decide +kernel

theorem fam57_sub24_ok : fam57.subOK 24 = true := by decide +kernel

theorem fam57_sub25_ok : fam57.subOK 25 = true := by decide +kernel

theorem fam57_sub26_ok : fam57.subOK 26 = true := by decide +kernel

theorem fam57_sub27_ok : fam57.subOK 27 = true := by decide +kernel

theorem fam57_sub28_ok : fam57.subOK 28 = true := by decide +kernel

theorem fam57_sub29_ok : fam57.subOK 29 = true := by decide +kernel

theorem fam57_sub30_ok : fam57.subOK 30 = true := by decide +kernel

theorem fam57_sub31_ok : fam57.subOK 31 = true := by decide +kernel

theorem fam57_sub32_ok : fam57.subOK 32 = true := by decide +kernel

theorem fam57_sub33_ok : fam57.subOK 33 = true := by decide +kernel

theorem fam57_sub34_ok : fam57.subOK 34 = true := by decide +kernel

theorem fam57_sub35_ok : fam57.subOK 35 = true := by decide +kernel

theorem fam57_sub36_ok : fam57.subOK 36 = true := by decide +kernel

theorem fam57_sub37_ok : fam57.subOK 37 = true := by decide +kernel

theorem fam57_sub38_ok : fam57.subOK 38 = true := by decide +kernel

theorem fam57_sub39_ok : fam57.subOK 39 = true := by decide +kernel

theorem fam57_sub40_ok : fam57.subOK 40 = true := by decide +kernel

theorem fam57_sub41_ok : fam57.subOK 41 = true := by decide +kernel

theorem fam57_sub42_ok : fam57.subOK 42 = true := by decide +kernel

theorem fam57_sub43_ok : fam57.subOK 43 = true := by decide +kernel

theorem fam57_sub44_ok : fam57.subOK 44 = true := by decide +kernel

theorem fam57_sub45_ok : fam57.subOK 45 = true := by decide +kernel

theorem fam57_sub46_ok : fam57.subOK 46 = true := by decide +kernel

theorem fam57_sub47_ok : fam57.subOK 47 = true := by decide +kernel

theorem fam57_sub48_ok : fam57.subOK 48 = true := by decide +kernel

theorem fam57_recs : ∀ r ∈ fam57.recs, fam57.recOK r = true :=
  fam57.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [fam57_recs_ok0, fam57_recs_ok1, fam57_recs_ok2, fam57_recs_ok3, fam57_recs_ok4, fam57_recs_ok5, fam57_recs_ok6, fam57_recs_ok7, fam57_recs_ok8, fam57_recs_ok9, fam57_recs_ok10, fam57_recs_ok11, fam57_recs_ok12])
    (by decide +kernel)

theorem fam57_subs : ∀ k < fam57.subs.length, fam57.subOK k = true := by
  intro k hk
  have h : fam57.subs.length = 49 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam57_sub0_ok, fam57_sub1_ok, fam57_sub2_ok, fam57_sub3_ok, fam57_sub4_ok, fam57_sub5_ok, fam57_sub6_ok, fam57_sub7_ok, fam57_sub8_ok, fam57_sub9_ok, fam57_sub10_ok, fam57_sub11_ok, fam57_sub12_ok, fam57_sub13_ok, fam57_sub14_ok, fam57_sub15_ok, fam57_sub16_ok, fam57_sub17_ok, fam57_sub18_ok, fam57_sub19_ok, fam57_sub20_ok, fam57_sub21_ok, fam57_sub22_ok, fam57_sub23_ok, fam57_sub24_ok, fam57_sub25_ok, fam57_sub26_ok, fam57_sub27_ok, fam57_sub28_ok, fam57_sub29_ok, fam57_sub30_ok, fam57_sub31_ok, fam57_sub32_ok, fam57_sub33_ok, fam57_sub34_ok, fam57_sub35_ok, fam57_sub36_ok, fam57_sub37_ok, fam57_sub38_ok, fam57_sub39_ok, fam57_sub40_ok, fam57_sub41_ok, fam57_sub42_ok, fam57_sub43_ok, fam57_sub44_ok, fam57_sub45_ok, fam57_sub46_ok, fam57_sub47_ok, fam57_sub48_ok]

end Kalai5.A16
