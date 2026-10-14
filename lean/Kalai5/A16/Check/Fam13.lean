import Kalai5.A16.Data.Fam13
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 13. -/

namespace Kalai5.A16

theorem fam13_check : fam13.check = true := by decide +kernel

theorem fam13_recs_ok0 : fam13.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam13_recs_ok1 : fam13.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam13_recs_ok2 : fam13.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam13_recs_ok3 : fam13.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam13_recs_ok4 : fam13.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam13_recs_ok5 : fam13.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam13_recs_ok6 : fam13.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam13_recs_ok7 : fam13.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam13_recs_ok8 : fam13.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam13_recs_ok9 : fam13.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam13_recs_ok10 : fam13.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam13_recs_ok11 : fam13.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam13_sub0_ok : fam13.subOK 0 = true := by decide +kernel

theorem fam13_sub1_ok : fam13.subOK 1 = true := by decide +kernel

theorem fam13_sub2_ok : fam13.subOK 2 = true := by decide +kernel

theorem fam13_sub3_ok : fam13.subOK 3 = true := by decide +kernel

theorem fam13_sub4_ok : fam13.subOK 4 = true := by decide +kernel

theorem fam13_sub5_ok : fam13.subOK 5 = true := by decide +kernel

theorem fam13_sub6_ok : fam13.subOK 6 = true := by decide +kernel

theorem fam13_sub7_ok : fam13.subOK 7 = true := by decide +kernel

theorem fam13_sub8_ok : fam13.subOK 8 = true := by decide +kernel

theorem fam13_sub9_ok : fam13.subOK 9 = true := by decide +kernel

theorem fam13_sub10_ok : fam13.subOK 10 = true := by decide +kernel

theorem fam13_sub11_ok : fam13.subOK 11 = true := by decide +kernel

theorem fam13_sub12_ok : fam13.subOK 12 = true := by decide +kernel

theorem fam13_sub13_ok : fam13.subOK 13 = true := by decide +kernel

theorem fam13_sub14_ok : fam13.subOK 14 = true := by decide +kernel

theorem fam13_sub15_ok : fam13.subOK 15 = true := by decide +kernel

theorem fam13_sub16_ok : fam13.subOK 16 = true := by decide +kernel

theorem fam13_sub17_ok : fam13.subOK 17 = true := by decide +kernel

theorem fam13_sub18_ok : fam13.subOK 18 = true := by decide +kernel

theorem fam13_sub19_ok : fam13.subOK 19 = true := by decide +kernel

theorem fam13_sub20_ok : fam13.subOK 20 = true := by decide +kernel

theorem fam13_sub21_ok : fam13.subOK 21 = true := by decide +kernel

theorem fam13_sub22_ok : fam13.subOK 22 = true := by decide +kernel

theorem fam13_sub23_ok : fam13.subOK 23 = true := by decide +kernel

theorem fam13_sub24_ok : fam13.subOK 24 = true := by decide +kernel

theorem fam13_sub25_ok : fam13.subOK 25 = true := by decide +kernel

theorem fam13_sub26_ok : fam13.subOK 26 = true := by decide +kernel

theorem fam13_sub27_ok : fam13.subOK 27 = true := by decide +kernel

theorem fam13_sub28_ok : fam13.subOK 28 = true := by decide +kernel

theorem fam13_sub29_ok : fam13.subOK 29 = true := by decide +kernel

theorem fam13_sub30_ok : fam13.subOK 30 = true := by decide +kernel

theorem fam13_sub31_ok : fam13.subOK 31 = true := by decide +kernel

theorem fam13_sub32_ok : fam13.subOK 32 = true := by decide +kernel

theorem fam13_sub33_ok : fam13.subOK 33 = true := by decide +kernel

theorem fam13_sub34_ok : fam13.subOK 34 = true := by decide +kernel

theorem fam13_sub35_ok : fam13.subOK 35 = true := by decide +kernel

theorem fam13_sub36_ok : fam13.subOK 36 = true := by decide +kernel

theorem fam13_sub37_ok : fam13.subOK 37 = true := by decide +kernel

theorem fam13_sub38_ok : fam13.subOK 38 = true := by decide +kernel

theorem fam13_sub39_ok : fam13.subOK 39 = true := by decide +kernel

theorem fam13_sub40_ok : fam13.subOK 40 = true := by decide +kernel

theorem fam13_sub41_ok : fam13.subOK 41 = true := by decide +kernel

theorem fam13_recs : ∀ r ∈ fam13.recs, fam13.recOK r = true :=
  fam13.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [fam13_recs_ok0, fam13_recs_ok1, fam13_recs_ok2, fam13_recs_ok3, fam13_recs_ok4, fam13_recs_ok5, fam13_recs_ok6, fam13_recs_ok7, fam13_recs_ok8, fam13_recs_ok9, fam13_recs_ok10, fam13_recs_ok11])
    (by decide +kernel)

theorem fam13_subs : ∀ k < fam13.subs.length, fam13.subOK k = true := by
  intro k hk
  have h : fam13.subs.length = 42 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam13_sub0_ok, fam13_sub1_ok, fam13_sub2_ok, fam13_sub3_ok, fam13_sub4_ok, fam13_sub5_ok, fam13_sub6_ok, fam13_sub7_ok, fam13_sub8_ok, fam13_sub9_ok, fam13_sub10_ok, fam13_sub11_ok, fam13_sub12_ok, fam13_sub13_ok, fam13_sub14_ok, fam13_sub15_ok, fam13_sub16_ok, fam13_sub17_ok, fam13_sub18_ok, fam13_sub19_ok, fam13_sub20_ok, fam13_sub21_ok, fam13_sub22_ok, fam13_sub23_ok, fam13_sub24_ok, fam13_sub25_ok, fam13_sub26_ok, fam13_sub27_ok, fam13_sub28_ok, fam13_sub29_ok, fam13_sub30_ok, fam13_sub31_ok, fam13_sub32_ok, fam13_sub33_ok, fam13_sub34_ok, fam13_sub35_ok, fam13_sub36_ok, fam13_sub37_ok, fam13_sub38_ok, fam13_sub39_ok, fam13_sub40_ok, fam13_sub41_ok]

end Kalai5.A16
