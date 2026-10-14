import Kalai5.A16.Data.Fam35
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 35. -/

namespace Kalai5.A16

theorem fam35_check : fam35.check = true := by decide +kernel

theorem fam35_recs_ok0 : fam35.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam35_recs_ok1 : fam35.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam35_recs_ok2 : fam35.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam35_recs_ok3 : fam35.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam35_recs_ok4 : fam35.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam35_recs_ok5 : fam35.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam35_recs_ok6 : fam35.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam35_recs_ok7 : fam35.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam35_recs_ok8 : fam35.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam35_recs_ok9 : fam35.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam35_recs_ok10 : fam35.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam35_recs_ok11 : fam35.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam35_sub0_ok : fam35.subOK 0 = true := by decide +kernel

theorem fam35_sub1_ok : fam35.subOK 1 = true := by decide +kernel

theorem fam35_sub2_ok : fam35.subOK 2 = true := by decide +kernel

theorem fam35_sub3_ok : fam35.subOK 3 = true := by decide +kernel

theorem fam35_sub4_ok : fam35.subOK 4 = true := by decide +kernel

theorem fam35_sub5_ok : fam35.subOK 5 = true := by decide +kernel

theorem fam35_sub6_ok : fam35.subOK 6 = true := by decide +kernel

theorem fam35_sub7_ok : fam35.subOK 7 = true := by decide +kernel

theorem fam35_sub8_ok : fam35.subOK 8 = true := by decide +kernel

theorem fam35_sub9_ok : fam35.subOK 9 = true := by decide +kernel

theorem fam35_sub10_ok : fam35.subOK 10 = true := by decide +kernel

theorem fam35_sub11_ok : fam35.subOK 11 = true := by decide +kernel

theorem fam35_sub12_ok : fam35.subOK 12 = true := by decide +kernel

theorem fam35_sub13_ok : fam35.subOK 13 = true := by decide +kernel

theorem fam35_sub14_ok : fam35.subOK 14 = true := by decide +kernel

theorem fam35_sub15_ok : fam35.subOK 15 = true := by decide +kernel

theorem fam35_sub16_ok : fam35.subOK 16 = true := by decide +kernel

theorem fam35_sub17_ok : fam35.subOK 17 = true := by decide +kernel

theorem fam35_sub18_ok : fam35.subOK 18 = true := by decide +kernel

theorem fam35_sub19_ok : fam35.subOK 19 = true := by decide +kernel

theorem fam35_sub20_ok : fam35.subOK 20 = true := by decide +kernel

theorem fam35_sub21_ok : fam35.subOK 21 = true := by decide +kernel

theorem fam35_sub22_ok : fam35.subOK 22 = true := by decide +kernel

theorem fam35_sub23_ok : fam35.subOK 23 = true := by decide +kernel

theorem fam35_sub24_ok : fam35.subOK 24 = true := by decide +kernel

theorem fam35_sub25_ok : fam35.subOK 25 = true := by decide +kernel

theorem fam35_sub26_ok : fam35.subOK 26 = true := by decide +kernel

theorem fam35_sub27_ok : fam35.subOK 27 = true := by decide +kernel

theorem fam35_sub28_ok : fam35.subOK 28 = true := by decide +kernel

theorem fam35_sub29_ok : fam35.subOK 29 = true := by decide +kernel

theorem fam35_sub30_ok : fam35.subOK 30 = true := by decide +kernel

theorem fam35_sub31_ok : fam35.subOK 31 = true := by decide +kernel

theorem fam35_sub32_ok : fam35.subOK 32 = true := by decide +kernel

theorem fam35_sub33_ok : fam35.subOK 33 = true := by decide +kernel

theorem fam35_sub34_ok : fam35.subOK 34 = true := by decide +kernel

theorem fam35_sub35_ok : fam35.subOK 35 = true := by decide +kernel

theorem fam35_sub36_ok : fam35.subOK 36 = true := by decide +kernel

theorem fam35_sub37_ok : fam35.subOK 37 = true := by decide +kernel

theorem fam35_sub38_ok : fam35.subOK 38 = true := by decide +kernel

theorem fam35_sub39_ok : fam35.subOK 39 = true := by decide +kernel

theorem fam35_recs : ∀ r ∈ fam35.recs, fam35.recOK r = true :=
  fam35.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [fam35_recs_ok0, fam35_recs_ok1, fam35_recs_ok2, fam35_recs_ok3, fam35_recs_ok4, fam35_recs_ok5, fam35_recs_ok6, fam35_recs_ok7, fam35_recs_ok8, fam35_recs_ok9, fam35_recs_ok10, fam35_recs_ok11])
    (by decide +kernel)

theorem fam35_subs : ∀ k < fam35.subs.length, fam35.subOK k = true := by
  intro k hk
  have h : fam35.subs.length = 40 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam35_sub0_ok, fam35_sub1_ok, fam35_sub2_ok, fam35_sub3_ok, fam35_sub4_ok, fam35_sub5_ok, fam35_sub6_ok, fam35_sub7_ok, fam35_sub8_ok, fam35_sub9_ok, fam35_sub10_ok, fam35_sub11_ok, fam35_sub12_ok, fam35_sub13_ok, fam35_sub14_ok, fam35_sub15_ok, fam35_sub16_ok, fam35_sub17_ok, fam35_sub18_ok, fam35_sub19_ok, fam35_sub20_ok, fam35_sub21_ok, fam35_sub22_ok, fam35_sub23_ok, fam35_sub24_ok, fam35_sub25_ok, fam35_sub26_ok, fam35_sub27_ok, fam35_sub28_ok, fam35_sub29_ok, fam35_sub30_ok, fam35_sub31_ok, fam35_sub32_ok, fam35_sub33_ok, fam35_sub34_ok, fam35_sub35_ok, fam35_sub36_ok, fam35_sub37_ok, fam35_sub38_ok, fam35_sub39_ok]

end Kalai5.A16
