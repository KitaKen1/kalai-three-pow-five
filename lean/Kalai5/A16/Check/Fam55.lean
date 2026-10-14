import Kalai5.A16.Data.Fam55
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 55. -/

namespace Kalai5.A16

theorem fam55_check : fam55.check = true := by decide +kernel

theorem fam55_recs_ok0 : fam55.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam55_recs_ok1 : fam55.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam55_recs_ok2 : fam55.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam55_recs_ok3 : fam55.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam55_recs_ok4 : fam55.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam55_recs_ok5 : fam55.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam55_recs_ok6 : fam55.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam55_recs_ok7 : fam55.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam55_recs_ok8 : fam55.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam55_recs_ok9 : fam55.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam55_recs_ok10 : fam55.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam55_recs_ok11 : fam55.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam55_sub0_ok : fam55.subOK 0 = true := by decide +kernel

theorem fam55_sub1_ok : fam55.subOK 1 = true := by decide +kernel

theorem fam55_sub2_ok : fam55.subOK 2 = true := by decide +kernel

theorem fam55_sub3_ok : fam55.subOK 3 = true := by decide +kernel

theorem fam55_sub4_ok : fam55.subOK 4 = true := by decide +kernel

theorem fam55_sub5_ok : fam55.subOK 5 = true := by decide +kernel

theorem fam55_sub6_ok : fam55.subOK 6 = true := by decide +kernel

theorem fam55_sub7_ok : fam55.subOK 7 = true := by decide +kernel

theorem fam55_sub8_ok : fam55.subOK 8 = true := by decide +kernel

theorem fam55_sub9_ok : fam55.subOK 9 = true := by decide +kernel

theorem fam55_sub10_ok : fam55.subOK 10 = true := by decide +kernel

theorem fam55_sub11_ok : fam55.subOK 11 = true := by decide +kernel

theorem fam55_sub12_ok : fam55.subOK 12 = true := by decide +kernel

theorem fam55_sub13_ok : fam55.subOK 13 = true := by decide +kernel

theorem fam55_sub14_ok : fam55.subOK 14 = true := by decide +kernel

theorem fam55_sub15_ok : fam55.subOK 15 = true := by decide +kernel

theorem fam55_sub16_ok : fam55.subOK 16 = true := by decide +kernel

theorem fam55_sub17_ok : fam55.subOK 17 = true := by decide +kernel

theorem fam55_sub18_ok : fam55.subOK 18 = true := by decide +kernel

theorem fam55_sub19_ok : fam55.subOK 19 = true := by decide +kernel

theorem fam55_sub20_ok : fam55.subOK 20 = true := by decide +kernel

theorem fam55_sub21_ok : fam55.subOK 21 = true := by decide +kernel

theorem fam55_sub22_ok : fam55.subOK 22 = true := by decide +kernel

theorem fam55_sub23_ok : fam55.subOK 23 = true := by decide +kernel

theorem fam55_sub24_ok : fam55.subOK 24 = true := by decide +kernel

theorem fam55_sub25_ok : fam55.subOK 25 = true := by decide +kernel

theorem fam55_sub26_ok : fam55.subOK 26 = true := by decide +kernel

theorem fam55_sub27_ok : fam55.subOK 27 = true := by decide +kernel

theorem fam55_sub28_ok : fam55.subOK 28 = true := by decide +kernel

theorem fam55_sub29_ok : fam55.subOK 29 = true := by decide +kernel

theorem fam55_sub30_ok : fam55.subOK 30 = true := by decide +kernel

theorem fam55_sub31_ok : fam55.subOK 31 = true := by decide +kernel

theorem fam55_sub32_ok : fam55.subOK 32 = true := by decide +kernel

theorem fam55_sub33_ok : fam55.subOK 33 = true := by decide +kernel

theorem fam55_sub34_ok : fam55.subOK 34 = true := by decide +kernel

theorem fam55_sub35_ok : fam55.subOK 35 = true := by decide +kernel

theorem fam55_sub36_ok : fam55.subOK 36 = true := by decide +kernel

theorem fam55_sub37_ok : fam55.subOK 37 = true := by decide +kernel

theorem fam55_sub38_ok : fam55.subOK 38 = true := by decide +kernel

theorem fam55_sub39_ok : fam55.subOK 39 = true := by decide +kernel

theorem fam55_sub40_ok : fam55.subOK 40 = true := by decide +kernel

theorem fam55_recs : ∀ r ∈ fam55.recs, fam55.recOK r = true :=
  fam55.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [fam55_recs_ok0, fam55_recs_ok1, fam55_recs_ok2, fam55_recs_ok3, fam55_recs_ok4, fam55_recs_ok5, fam55_recs_ok6, fam55_recs_ok7, fam55_recs_ok8, fam55_recs_ok9, fam55_recs_ok10, fam55_recs_ok11])
    (by decide +kernel)

theorem fam55_subs : ∀ k < fam55.subs.length, fam55.subOK k = true := by
  intro k hk
  have h : fam55.subs.length = 41 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam55_sub0_ok, fam55_sub1_ok, fam55_sub2_ok, fam55_sub3_ok, fam55_sub4_ok, fam55_sub5_ok, fam55_sub6_ok, fam55_sub7_ok, fam55_sub8_ok, fam55_sub9_ok, fam55_sub10_ok, fam55_sub11_ok, fam55_sub12_ok, fam55_sub13_ok, fam55_sub14_ok, fam55_sub15_ok, fam55_sub16_ok, fam55_sub17_ok, fam55_sub18_ok, fam55_sub19_ok, fam55_sub20_ok, fam55_sub21_ok, fam55_sub22_ok, fam55_sub23_ok, fam55_sub24_ok, fam55_sub25_ok, fam55_sub26_ok, fam55_sub27_ok, fam55_sub28_ok, fam55_sub29_ok, fam55_sub30_ok, fam55_sub31_ok, fam55_sub32_ok, fam55_sub33_ok, fam55_sub34_ok, fam55_sub35_ok, fam55_sub36_ok, fam55_sub37_ok, fam55_sub38_ok, fam55_sub39_ok, fam55_sub40_ok]

end Kalai5.A16
