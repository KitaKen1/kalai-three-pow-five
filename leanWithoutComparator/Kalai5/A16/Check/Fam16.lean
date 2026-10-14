import Kalai5.A16.Data.Fam16
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 16. -/

namespace Kalai5.A16

theorem fam16_check : fam16.check = true := by decide +kernel

theorem fam16_recs_ok0 : fam16.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam16_recs_ok1 : fam16.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam16_recs_ok2 : fam16.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam16_recs_ok3 : fam16.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam16_recs_ok4 : fam16.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam16_recs_ok5 : fam16.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam16_recs_ok6 : fam16.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam16_recs_ok7 : fam16.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam16_recs_ok8 : fam16.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam16_recs_ok9 : fam16.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam16_recs_ok10 : fam16.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam16_recs_ok11 : fam16.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam16_sub0_ok : fam16.subOK 0 = true := by decide +kernel

theorem fam16_sub1_ok : fam16.subOK 1 = true := by decide +kernel

theorem fam16_sub2_ok : fam16.subOK 2 = true := by decide +kernel

theorem fam16_sub3_ok : fam16.subOK 3 = true := by decide +kernel

theorem fam16_sub4_ok : fam16.subOK 4 = true := by decide +kernel

theorem fam16_sub5_ok : fam16.subOK 5 = true := by decide +kernel

theorem fam16_sub6_ok : fam16.subOK 6 = true := by decide +kernel

theorem fam16_sub7_ok : fam16.subOK 7 = true := by decide +kernel

theorem fam16_sub8_ok : fam16.subOK 8 = true := by decide +kernel

theorem fam16_sub9_ok : fam16.subOK 9 = true := by decide +kernel

theorem fam16_sub10_ok : fam16.subOK 10 = true := by decide +kernel

theorem fam16_sub11_ok : fam16.subOK 11 = true := by decide +kernel

theorem fam16_sub12_ok : fam16.subOK 12 = true := by decide +kernel

theorem fam16_sub13_ok : fam16.subOK 13 = true := by decide +kernel

theorem fam16_sub14_ok : fam16.subOK 14 = true := by decide +kernel

theorem fam16_sub15_ok : fam16.subOK 15 = true := by decide +kernel

theorem fam16_sub16_ok : fam16.subOK 16 = true := by decide +kernel

theorem fam16_sub17_ok : fam16.subOK 17 = true := by decide +kernel

theorem fam16_sub18_ok : fam16.subOK 18 = true := by decide +kernel

theorem fam16_sub19_ok : fam16.subOK 19 = true := by decide +kernel

theorem fam16_sub20_ok : fam16.subOK 20 = true := by decide +kernel

theorem fam16_sub21_ok : fam16.subOK 21 = true := by decide +kernel

theorem fam16_sub22_ok : fam16.subOK 22 = true := by decide +kernel

theorem fam16_sub23_ok : fam16.subOK 23 = true := by decide +kernel

theorem fam16_sub24_ok : fam16.subOK 24 = true := by decide +kernel

theorem fam16_sub25_ok : fam16.subOK 25 = true := by decide +kernel

theorem fam16_sub26_ok : fam16.subOK 26 = true := by decide +kernel

theorem fam16_sub27_ok : fam16.subOK 27 = true := by decide +kernel

theorem fam16_sub28_ok : fam16.subOK 28 = true := by decide +kernel

theorem fam16_sub29_ok : fam16.subOK 29 = true := by decide +kernel

theorem fam16_sub30_ok : fam16.subOK 30 = true := by decide +kernel

theorem fam16_sub31_ok : fam16.subOK 31 = true := by decide +kernel

theorem fam16_sub32_ok : fam16.subOK 32 = true := by decide +kernel

theorem fam16_sub33_ok : fam16.subOK 33 = true := by decide +kernel

theorem fam16_sub34_ok : fam16.subOK 34 = true := by decide +kernel

theorem fam16_sub35_ok : fam16.subOK 35 = true := by decide +kernel

theorem fam16_sub36_ok : fam16.subOK 36 = true := by decide +kernel

theorem fam16_sub37_ok : fam16.subOK 37 = true := by decide +kernel

theorem fam16_sub38_ok : fam16.subOK 38 = true := by decide +kernel

theorem fam16_sub39_ok : fam16.subOK 39 = true := by decide +kernel

theorem fam16_sub40_ok : fam16.subOK 40 = true := by decide +kernel

theorem fam16_sub41_ok : fam16.subOK 41 = true := by decide +kernel

theorem fam16_sub42_ok : fam16.subOK 42 = true := by decide +kernel

theorem fam16_sub43_ok : fam16.subOK 43 = true := by decide +kernel

theorem fam16_sub44_ok : fam16.subOK 44 = true := by decide +kernel

theorem fam16_sub45_ok : fam16.subOK 45 = true := by decide +kernel

theorem fam16_sub46_ok : fam16.subOK 46 = true := by decide +kernel

theorem fam16_sub47_ok : fam16.subOK 47 = true := by decide +kernel

theorem fam16_sub48_ok : fam16.subOK 48 = true := by decide +kernel

theorem fam16_sub49_ok : fam16.subOK 49 = true := by decide +kernel

theorem fam16_sub50_ok : fam16.subOK 50 = true := by decide +kernel

theorem fam16_recs : ∀ r ∈ fam16.recs, fam16.recOK r = true :=
  fam16.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [fam16_recs_ok0, fam16_recs_ok1, fam16_recs_ok2, fam16_recs_ok3, fam16_recs_ok4, fam16_recs_ok5, fam16_recs_ok6, fam16_recs_ok7, fam16_recs_ok8, fam16_recs_ok9, fam16_recs_ok10, fam16_recs_ok11])
    (by decide +kernel)

theorem fam16_subs : ∀ k < fam16.subs.length, fam16.subOK k = true := by
  intro k hk
  have h : fam16.subs.length = 51 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam16_sub0_ok, fam16_sub1_ok, fam16_sub2_ok, fam16_sub3_ok, fam16_sub4_ok, fam16_sub5_ok, fam16_sub6_ok, fam16_sub7_ok, fam16_sub8_ok, fam16_sub9_ok, fam16_sub10_ok, fam16_sub11_ok, fam16_sub12_ok, fam16_sub13_ok, fam16_sub14_ok, fam16_sub15_ok, fam16_sub16_ok, fam16_sub17_ok, fam16_sub18_ok, fam16_sub19_ok, fam16_sub20_ok, fam16_sub21_ok, fam16_sub22_ok, fam16_sub23_ok, fam16_sub24_ok, fam16_sub25_ok, fam16_sub26_ok, fam16_sub27_ok, fam16_sub28_ok, fam16_sub29_ok, fam16_sub30_ok, fam16_sub31_ok, fam16_sub32_ok, fam16_sub33_ok, fam16_sub34_ok, fam16_sub35_ok, fam16_sub36_ok, fam16_sub37_ok, fam16_sub38_ok, fam16_sub39_ok, fam16_sub40_ok, fam16_sub41_ok, fam16_sub42_ok, fam16_sub43_ok, fam16_sub44_ok, fam16_sub45_ok, fam16_sub46_ok, fam16_sub47_ok, fam16_sub48_ok, fam16_sub49_ok, fam16_sub50_ok]

end Kalai5.A16
