import Kalai5.A16.Data.Fam23
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 23. -/

namespace Kalai5.A16

theorem fam23_check : fam23.check = true := by decide +kernel

theorem fam23_recs_ok0 : fam23.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam23_recs_ok1 : fam23.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam23_recs_ok2 : fam23.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam23_recs_ok3 : fam23.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam23_recs_ok4 : fam23.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam23_recs_ok5 : fam23.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam23_recs_ok6 : fam23.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam23_recs_ok7 : fam23.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam23_recs_ok8 : fam23.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam23_recs_ok9 : fam23.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam23_recs_ok10 : fam23.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam23_recs_ok11 : fam23.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam23_recs_ok12 : fam23.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam23_recs_ok13 : fam23.recsOK (40 * 13) 40 = true := by decide +kernel

theorem fam23_sub0_ok : fam23.subOK 0 = true := by decide +kernel

theorem fam23_sub1_ok : fam23.subOK 1 = true := by decide +kernel

theorem fam23_sub2_ok : fam23.subOK 2 = true := by decide +kernel

theorem fam23_sub3_ok : fam23.subOK 3 = true := by decide +kernel

theorem fam23_sub4_ok : fam23.subOK 4 = true := by decide +kernel

theorem fam23_sub5_ok : fam23.subOK 5 = true := by decide +kernel

theorem fam23_sub6_ok : fam23.subOK 6 = true := by decide +kernel

theorem fam23_sub7_ok : fam23.subOK 7 = true := by decide +kernel

theorem fam23_sub8_ok : fam23.subOK 8 = true := by decide +kernel

theorem fam23_sub9_ok : fam23.subOK 9 = true := by decide +kernel

theorem fam23_sub10_ok : fam23.subOK 10 = true := by decide +kernel

theorem fam23_sub11_ok : fam23.subOK 11 = true := by decide +kernel

theorem fam23_sub12_ok : fam23.subOK 12 = true := by decide +kernel

theorem fam23_sub13_ok : fam23.subOK 13 = true := by decide +kernel

theorem fam23_sub14_ok : fam23.subOK 14 = true := by decide +kernel

theorem fam23_sub15_ok : fam23.subOK 15 = true := by decide +kernel

theorem fam23_sub16_ok : fam23.subOK 16 = true := by decide +kernel

theorem fam23_sub17_ok : fam23.subOK 17 = true := by decide +kernel

theorem fam23_sub18_ok : fam23.subOK 18 = true := by decide +kernel

theorem fam23_sub19_ok : fam23.subOK 19 = true := by decide +kernel

theorem fam23_sub20_ok : fam23.subOK 20 = true := by decide +kernel

theorem fam23_sub21_ok : fam23.subOK 21 = true := by decide +kernel

theorem fam23_sub22_ok : fam23.subOK 22 = true := by decide +kernel

theorem fam23_sub23_ok : fam23.subOK 23 = true := by decide +kernel

theorem fam23_sub24_ok : fam23.subOK 24 = true := by decide +kernel

theorem fam23_sub25_ok : fam23.subOK 25 = true := by decide +kernel

theorem fam23_sub26_ok : fam23.subOK 26 = true := by decide +kernel

theorem fam23_sub27_ok : fam23.subOK 27 = true := by decide +kernel

theorem fam23_sub28_ok : fam23.subOK 28 = true := by decide +kernel

theorem fam23_sub29_ok : fam23.subOK 29 = true := by decide +kernel

theorem fam23_sub30_ok : fam23.subOK 30 = true := by decide +kernel

theorem fam23_sub31_ok : fam23.subOK 31 = true := by decide +kernel

theorem fam23_sub32_ok : fam23.subOK 32 = true := by decide +kernel

theorem fam23_sub33_ok : fam23.subOK 33 = true := by decide +kernel

theorem fam23_sub34_ok : fam23.subOK 34 = true := by decide +kernel

theorem fam23_sub35_ok : fam23.subOK 35 = true := by decide +kernel

theorem fam23_sub36_ok : fam23.subOK 36 = true := by decide +kernel

theorem fam23_sub37_ok : fam23.subOK 37 = true := by decide +kernel

theorem fam23_sub38_ok : fam23.subOK 38 = true := by decide +kernel

theorem fam23_sub39_ok : fam23.subOK 39 = true := by decide +kernel

theorem fam23_sub40_ok : fam23.subOK 40 = true := by decide +kernel

theorem fam23_sub41_ok : fam23.subOK 41 = true := by decide +kernel

theorem fam23_sub42_ok : fam23.subOK 42 = true := by decide +kernel

theorem fam23_sub43_ok : fam23.subOK 43 = true := by decide +kernel

theorem fam23_sub44_ok : fam23.subOK 44 = true := by decide +kernel

theorem fam23_sub45_ok : fam23.subOK 45 = true := by decide +kernel

theorem fam23_sub46_ok : fam23.subOK 46 = true := by decide +kernel

theorem fam23_sub47_ok : fam23.subOK 47 = true := by decide +kernel

theorem fam23_sub48_ok : fam23.subOK 48 = true := by decide +kernel

theorem fam23_sub49_ok : fam23.subOK 49 = true := by decide +kernel

theorem fam23_recs : ∀ r ∈ fam23.recs, fam23.recOK r = true :=
  fam23.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [fam23_recs_ok0, fam23_recs_ok1, fam23_recs_ok2, fam23_recs_ok3, fam23_recs_ok4, fam23_recs_ok5, fam23_recs_ok6, fam23_recs_ok7, fam23_recs_ok8, fam23_recs_ok9, fam23_recs_ok10, fam23_recs_ok11, fam23_recs_ok12, fam23_recs_ok13])
    (by decide +kernel)

theorem fam23_subs : ∀ k < fam23.subs.length, fam23.subOK k = true := by
  intro k hk
  have h : fam23.subs.length = 50 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam23_sub0_ok, fam23_sub1_ok, fam23_sub2_ok, fam23_sub3_ok, fam23_sub4_ok, fam23_sub5_ok, fam23_sub6_ok, fam23_sub7_ok, fam23_sub8_ok, fam23_sub9_ok, fam23_sub10_ok, fam23_sub11_ok, fam23_sub12_ok, fam23_sub13_ok, fam23_sub14_ok, fam23_sub15_ok, fam23_sub16_ok, fam23_sub17_ok, fam23_sub18_ok, fam23_sub19_ok, fam23_sub20_ok, fam23_sub21_ok, fam23_sub22_ok, fam23_sub23_ok, fam23_sub24_ok, fam23_sub25_ok, fam23_sub26_ok, fam23_sub27_ok, fam23_sub28_ok, fam23_sub29_ok, fam23_sub30_ok, fam23_sub31_ok, fam23_sub32_ok, fam23_sub33_ok, fam23_sub34_ok, fam23_sub35_ok, fam23_sub36_ok, fam23_sub37_ok, fam23_sub38_ok, fam23_sub39_ok, fam23_sub40_ok, fam23_sub41_ok, fam23_sub42_ok, fam23_sub43_ok, fam23_sub44_ok, fam23_sub45_ok, fam23_sub46_ok, fam23_sub47_ok, fam23_sub48_ok, fam23_sub49_ok]

end Kalai5.A16
