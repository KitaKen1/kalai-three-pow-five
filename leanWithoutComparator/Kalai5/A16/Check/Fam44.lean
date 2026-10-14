import Kalai5.A16.Data.Fam44
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 44. -/

namespace Kalai5.A16

theorem fam44_check : fam44.check = true := by decide +kernel

theorem fam44_recs_ok0 : fam44.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam44_recs_ok1 : fam44.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam44_recs_ok2 : fam44.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam44_recs_ok3 : fam44.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam44_recs_ok4 : fam44.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam44_recs_ok5 : fam44.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam44_recs_ok6 : fam44.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam44_recs_ok7 : fam44.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam44_recs_ok8 : fam44.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam44_recs_ok9 : fam44.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam44_recs_ok10 : fam44.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam44_recs_ok11 : fam44.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam44_recs_ok12 : fam44.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam44_sub0_ok : fam44.subOK 0 = true := by decide +kernel

theorem fam44_sub1_ok : fam44.subOK 1 = true := by decide +kernel

theorem fam44_sub2_ok : fam44.subOK 2 = true := by decide +kernel

theorem fam44_sub3_ok : fam44.subOK 3 = true := by decide +kernel

theorem fam44_sub4_ok : fam44.subOK 4 = true := by decide +kernel

theorem fam44_sub5_ok : fam44.subOK 5 = true := by decide +kernel

theorem fam44_sub6_ok : fam44.subOK 6 = true := by decide +kernel

theorem fam44_sub7_ok : fam44.subOK 7 = true := by decide +kernel

theorem fam44_sub8_ok : fam44.subOK 8 = true := by decide +kernel

theorem fam44_sub9_ok : fam44.subOK 9 = true := by decide +kernel

theorem fam44_sub10_ok : fam44.subOK 10 = true := by decide +kernel

theorem fam44_sub11_ok : fam44.subOK 11 = true := by decide +kernel

theorem fam44_sub12_ok : fam44.subOK 12 = true := by decide +kernel

theorem fam44_sub13_ok : fam44.subOK 13 = true := by decide +kernel

theorem fam44_sub14_ok : fam44.subOK 14 = true := by decide +kernel

theorem fam44_sub15_ok : fam44.subOK 15 = true := by decide +kernel

theorem fam44_sub16_ok : fam44.subOK 16 = true := by decide +kernel

theorem fam44_sub17_ok : fam44.subOK 17 = true := by decide +kernel

theorem fam44_sub18_ok : fam44.subOK 18 = true := by decide +kernel

theorem fam44_sub19_ok : fam44.subOK 19 = true := by decide +kernel

theorem fam44_sub20_ok : fam44.subOK 20 = true := by decide +kernel

theorem fam44_sub21_ok : fam44.subOK 21 = true := by decide +kernel

theorem fam44_sub22_ok : fam44.subOK 22 = true := by decide +kernel

theorem fam44_sub23_ok : fam44.subOK 23 = true := by decide +kernel

theorem fam44_sub24_ok : fam44.subOK 24 = true := by decide +kernel

theorem fam44_sub25_ok : fam44.subOK 25 = true := by decide +kernel

theorem fam44_sub26_ok : fam44.subOK 26 = true := by decide +kernel

theorem fam44_sub27_ok : fam44.subOK 27 = true := by decide +kernel

theorem fam44_sub28_ok : fam44.subOK 28 = true := by decide +kernel

theorem fam44_sub29_ok : fam44.subOK 29 = true := by decide +kernel

theorem fam44_sub30_ok : fam44.subOK 30 = true := by decide +kernel

theorem fam44_sub31_ok : fam44.subOK 31 = true := by decide +kernel

theorem fam44_sub32_ok : fam44.subOK 32 = true := by decide +kernel

theorem fam44_sub33_ok : fam44.subOK 33 = true := by decide +kernel

theorem fam44_sub34_ok : fam44.subOK 34 = true := by decide +kernel

theorem fam44_sub35_ok : fam44.subOK 35 = true := by decide +kernel

theorem fam44_sub36_ok : fam44.subOK 36 = true := by decide +kernel

theorem fam44_sub37_ok : fam44.subOK 37 = true := by decide +kernel

theorem fam44_sub38_ok : fam44.subOK 38 = true := by decide +kernel

theorem fam44_sub39_ok : fam44.subOK 39 = true := by decide +kernel

theorem fam44_recs : ∀ r ∈ fam44.recs, fam44.recOK r = true :=
  fam44.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [fam44_recs_ok0, fam44_recs_ok1, fam44_recs_ok2, fam44_recs_ok3, fam44_recs_ok4, fam44_recs_ok5, fam44_recs_ok6, fam44_recs_ok7, fam44_recs_ok8, fam44_recs_ok9, fam44_recs_ok10, fam44_recs_ok11, fam44_recs_ok12])
    (by decide +kernel)

theorem fam44_subs : ∀ k < fam44.subs.length, fam44.subOK k = true := by
  intro k hk
  have h : fam44.subs.length = 40 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam44_sub0_ok, fam44_sub1_ok, fam44_sub2_ok, fam44_sub3_ok, fam44_sub4_ok, fam44_sub5_ok, fam44_sub6_ok, fam44_sub7_ok, fam44_sub8_ok, fam44_sub9_ok, fam44_sub10_ok, fam44_sub11_ok, fam44_sub12_ok, fam44_sub13_ok, fam44_sub14_ok, fam44_sub15_ok, fam44_sub16_ok, fam44_sub17_ok, fam44_sub18_ok, fam44_sub19_ok, fam44_sub20_ok, fam44_sub21_ok, fam44_sub22_ok, fam44_sub23_ok, fam44_sub24_ok, fam44_sub25_ok, fam44_sub26_ok, fam44_sub27_ok, fam44_sub28_ok, fam44_sub29_ok, fam44_sub30_ok, fam44_sub31_ok, fam44_sub32_ok, fam44_sub33_ok, fam44_sub34_ok, fam44_sub35_ok, fam44_sub36_ok, fam44_sub37_ok, fam44_sub38_ok, fam44_sub39_ok]

end Kalai5.A16
