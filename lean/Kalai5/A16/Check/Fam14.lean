import Kalai5.A16.Data.Fam14
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 14. -/

namespace Kalai5.A16

theorem fam14_check : fam14.check = true := by decide +kernel

theorem fam14_recs_ok0 : fam14.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam14_recs_ok1 : fam14.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam14_recs_ok2 : fam14.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam14_recs_ok3 : fam14.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam14_recs_ok4 : fam14.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam14_recs_ok5 : fam14.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam14_recs_ok6 : fam14.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam14_recs_ok7 : fam14.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam14_recs_ok8 : fam14.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam14_recs_ok9 : fam14.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam14_recs_ok10 : fam14.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam14_recs_ok11 : fam14.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam14_sub0_ok : fam14.subOK 0 = true := by decide +kernel

theorem fam14_sub1_ok : fam14.subOK 1 = true := by decide +kernel

theorem fam14_sub2_ok : fam14.subOK 2 = true := by decide +kernel

theorem fam14_sub3_ok : fam14.subOK 3 = true := by decide +kernel

theorem fam14_sub4_ok : fam14.subOK 4 = true := by decide +kernel

theorem fam14_sub5_ok : fam14.subOK 5 = true := by decide +kernel

theorem fam14_sub6_ok : fam14.subOK 6 = true := by decide +kernel

theorem fam14_sub7_ok : fam14.subOK 7 = true := by decide +kernel

theorem fam14_sub8_ok : fam14.subOK 8 = true := by decide +kernel

theorem fam14_sub9_ok : fam14.subOK 9 = true := by decide +kernel

theorem fam14_sub10_ok : fam14.subOK 10 = true := by decide +kernel

theorem fam14_sub11_ok : fam14.subOK 11 = true := by decide +kernel

theorem fam14_sub12_ok : fam14.subOK 12 = true := by decide +kernel

theorem fam14_sub13_ok : fam14.subOK 13 = true := by decide +kernel

theorem fam14_sub14_ok : fam14.subOK 14 = true := by decide +kernel

theorem fam14_sub15_ok : fam14.subOK 15 = true := by decide +kernel

theorem fam14_sub16_ok : fam14.subOK 16 = true := by decide +kernel

theorem fam14_sub17_ok : fam14.subOK 17 = true := by decide +kernel

theorem fam14_sub18_ok : fam14.subOK 18 = true := by decide +kernel

theorem fam14_sub19_ok : fam14.subOK 19 = true := by decide +kernel

theorem fam14_sub20_ok : fam14.subOK 20 = true := by decide +kernel

theorem fam14_sub21_ok : fam14.subOK 21 = true := by decide +kernel

theorem fam14_sub22_ok : fam14.subOK 22 = true := by decide +kernel

theorem fam14_sub23_ok : fam14.subOK 23 = true := by decide +kernel

theorem fam14_sub24_ok : fam14.subOK 24 = true := by decide +kernel

theorem fam14_sub25_ok : fam14.subOK 25 = true := by decide +kernel

theorem fam14_sub26_ok : fam14.subOK 26 = true := by decide +kernel

theorem fam14_sub27_ok : fam14.subOK 27 = true := by decide +kernel

theorem fam14_sub28_ok : fam14.subOK 28 = true := by decide +kernel

theorem fam14_sub29_ok : fam14.subOK 29 = true := by decide +kernel

theorem fam14_sub30_ok : fam14.subOK 30 = true := by decide +kernel

theorem fam14_sub31_ok : fam14.subOK 31 = true := by decide +kernel

theorem fam14_sub32_ok : fam14.subOK 32 = true := by decide +kernel

theorem fam14_sub33_ok : fam14.subOK 33 = true := by decide +kernel

theorem fam14_sub34_ok : fam14.subOK 34 = true := by decide +kernel

theorem fam14_sub35_ok : fam14.subOK 35 = true := by decide +kernel

theorem fam14_sub36_ok : fam14.subOK 36 = true := by decide +kernel

theorem fam14_sub37_ok : fam14.subOK 37 = true := by decide +kernel

theorem fam14_sub38_ok : fam14.subOK 38 = true := by decide +kernel

theorem fam14_sub39_ok : fam14.subOK 39 = true := by decide +kernel

theorem fam14_sub40_ok : fam14.subOK 40 = true := by decide +kernel

theorem fam14_sub41_ok : fam14.subOK 41 = true := by decide +kernel

theorem fam14_sub42_ok : fam14.subOK 42 = true := by decide +kernel

theorem fam14_sub43_ok : fam14.subOK 43 = true := by decide +kernel

theorem fam14_sub44_ok : fam14.subOK 44 = true := by decide +kernel

theorem fam14_recs : ∀ r ∈ fam14.recs, fam14.recOK r = true :=
  fam14.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [fam14_recs_ok0, fam14_recs_ok1, fam14_recs_ok2, fam14_recs_ok3, fam14_recs_ok4, fam14_recs_ok5, fam14_recs_ok6, fam14_recs_ok7, fam14_recs_ok8, fam14_recs_ok9, fam14_recs_ok10, fam14_recs_ok11])
    (by decide +kernel)

theorem fam14_subs : ∀ k < fam14.subs.length, fam14.subOK k = true := by
  intro k hk
  have h : fam14.subs.length = 45 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam14_sub0_ok, fam14_sub1_ok, fam14_sub2_ok, fam14_sub3_ok, fam14_sub4_ok, fam14_sub5_ok, fam14_sub6_ok, fam14_sub7_ok, fam14_sub8_ok, fam14_sub9_ok, fam14_sub10_ok, fam14_sub11_ok, fam14_sub12_ok, fam14_sub13_ok, fam14_sub14_ok, fam14_sub15_ok, fam14_sub16_ok, fam14_sub17_ok, fam14_sub18_ok, fam14_sub19_ok, fam14_sub20_ok, fam14_sub21_ok, fam14_sub22_ok, fam14_sub23_ok, fam14_sub24_ok, fam14_sub25_ok, fam14_sub26_ok, fam14_sub27_ok, fam14_sub28_ok, fam14_sub29_ok, fam14_sub30_ok, fam14_sub31_ok, fam14_sub32_ok, fam14_sub33_ok, fam14_sub34_ok, fam14_sub35_ok, fam14_sub36_ok, fam14_sub37_ok, fam14_sub38_ok, fam14_sub39_ok, fam14_sub40_ok, fam14_sub41_ok, fam14_sub42_ok, fam14_sub43_ok, fam14_sub44_ok]

end Kalai5.A16
