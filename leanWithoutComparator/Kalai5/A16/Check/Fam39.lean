import Kalai5.A16.Data.Fam39
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 39. -/

namespace Kalai5.A16

theorem fam39_check : fam39.check = true := by decide +kernel

theorem fam39_recs_ok0 : fam39.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam39_recs_ok1 : fam39.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam39_recs_ok2 : fam39.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam39_recs_ok3 : fam39.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam39_recs_ok4 : fam39.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam39_recs_ok5 : fam39.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam39_recs_ok6 : fam39.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam39_recs_ok7 : fam39.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam39_recs_ok8 : fam39.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam39_recs_ok9 : fam39.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam39_recs_ok10 : fam39.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam39_sub0_ok : fam39.subOK 0 = true := by decide +kernel

theorem fam39_sub1_ok : fam39.subOK 1 = true := by decide +kernel

theorem fam39_sub2_ok : fam39.subOK 2 = true := by decide +kernel

theorem fam39_sub3_ok : fam39.subOK 3 = true := by decide +kernel

theorem fam39_sub4_ok : fam39.subOK 4 = true := by decide +kernel

theorem fam39_sub5_ok : fam39.subOK 5 = true := by decide +kernel

theorem fam39_sub6_ok : fam39.subOK 6 = true := by decide +kernel

theorem fam39_sub7_ok : fam39.subOK 7 = true := by decide +kernel

theorem fam39_sub8_ok : fam39.subOK 8 = true := by decide +kernel

theorem fam39_sub9_ok : fam39.subOK 9 = true := by decide +kernel

theorem fam39_sub10_ok : fam39.subOK 10 = true := by decide +kernel

theorem fam39_sub11_ok : fam39.subOK 11 = true := by decide +kernel

theorem fam39_sub12_ok : fam39.subOK 12 = true := by decide +kernel

theorem fam39_sub13_ok : fam39.subOK 13 = true := by decide +kernel

theorem fam39_sub14_ok : fam39.subOK 14 = true := by decide +kernel

theorem fam39_sub15_ok : fam39.subOK 15 = true := by decide +kernel

theorem fam39_sub16_ok : fam39.subOK 16 = true := by decide +kernel

theorem fam39_sub17_ok : fam39.subOK 17 = true := by decide +kernel

theorem fam39_sub18_ok : fam39.subOK 18 = true := by decide +kernel

theorem fam39_sub19_ok : fam39.subOK 19 = true := by decide +kernel

theorem fam39_sub20_ok : fam39.subOK 20 = true := by decide +kernel

theorem fam39_sub21_ok : fam39.subOK 21 = true := by decide +kernel

theorem fam39_sub22_ok : fam39.subOK 22 = true := by decide +kernel

theorem fam39_sub23_ok : fam39.subOK 23 = true := by decide +kernel

theorem fam39_sub24_ok : fam39.subOK 24 = true := by decide +kernel

theorem fam39_sub25_ok : fam39.subOK 25 = true := by decide +kernel

theorem fam39_sub26_ok : fam39.subOK 26 = true := by decide +kernel

theorem fam39_sub27_ok : fam39.subOK 27 = true := by decide +kernel

theorem fam39_sub28_ok : fam39.subOK 28 = true := by decide +kernel

theorem fam39_sub29_ok : fam39.subOK 29 = true := by decide +kernel

theorem fam39_sub30_ok : fam39.subOK 30 = true := by decide +kernel

theorem fam39_sub31_ok : fam39.subOK 31 = true := by decide +kernel

theorem fam39_sub32_ok : fam39.subOK 32 = true := by decide +kernel

theorem fam39_sub33_ok : fam39.subOK 33 = true := by decide +kernel

theorem fam39_sub34_ok : fam39.subOK 34 = true := by decide +kernel

theorem fam39_sub35_ok : fam39.subOK 35 = true := by decide +kernel

theorem fam39_sub36_ok : fam39.subOK 36 = true := by decide +kernel

theorem fam39_sub37_ok : fam39.subOK 37 = true := by decide +kernel

theorem fam39_sub38_ok : fam39.subOK 38 = true := by decide +kernel

theorem fam39_sub39_ok : fam39.subOK 39 = true := by decide +kernel

theorem fam39_recs : ∀ r ∈ fam39.recs, fam39.recOK r = true :=
  fam39.recs_of_chunks 11 (fun c hc => by
    interval_cases c
    exacts [fam39_recs_ok0, fam39_recs_ok1, fam39_recs_ok2, fam39_recs_ok3, fam39_recs_ok4, fam39_recs_ok5, fam39_recs_ok6, fam39_recs_ok7, fam39_recs_ok8, fam39_recs_ok9, fam39_recs_ok10])
    (by decide +kernel)

theorem fam39_subs : ∀ k < fam39.subs.length, fam39.subOK k = true := by
  intro k hk
  have h : fam39.subs.length = 40 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam39_sub0_ok, fam39_sub1_ok, fam39_sub2_ok, fam39_sub3_ok, fam39_sub4_ok, fam39_sub5_ok, fam39_sub6_ok, fam39_sub7_ok, fam39_sub8_ok, fam39_sub9_ok, fam39_sub10_ok, fam39_sub11_ok, fam39_sub12_ok, fam39_sub13_ok, fam39_sub14_ok, fam39_sub15_ok, fam39_sub16_ok, fam39_sub17_ok, fam39_sub18_ok, fam39_sub19_ok, fam39_sub20_ok, fam39_sub21_ok, fam39_sub22_ok, fam39_sub23_ok, fam39_sub24_ok, fam39_sub25_ok, fam39_sub26_ok, fam39_sub27_ok, fam39_sub28_ok, fam39_sub29_ok, fam39_sub30_ok, fam39_sub31_ok, fam39_sub32_ok, fam39_sub33_ok, fam39_sub34_ok, fam39_sub35_ok, fam39_sub36_ok, fam39_sub37_ok, fam39_sub38_ok, fam39_sub39_ok]

end Kalai5.A16
