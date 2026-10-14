import Kalai5.A16.Data.Fam41
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 41. -/

namespace Kalai5.A16

theorem fam41_check : fam41.check = true := by decide +kernel

theorem fam41_recs_ok0 : fam41.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam41_recs_ok1 : fam41.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam41_recs_ok2 : fam41.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam41_recs_ok3 : fam41.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam41_recs_ok4 : fam41.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam41_recs_ok5 : fam41.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam41_recs_ok6 : fam41.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam41_recs_ok7 : fam41.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam41_recs_ok8 : fam41.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam41_recs_ok9 : fam41.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam41_recs_ok10 : fam41.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam41_sub0_ok : fam41.subOK 0 = true := by decide +kernel

theorem fam41_sub1_ok : fam41.subOK 1 = true := by decide +kernel

theorem fam41_sub2_ok : fam41.subOK 2 = true := by decide +kernel

theorem fam41_sub3_ok : fam41.subOK 3 = true := by decide +kernel

theorem fam41_sub4_ok : fam41.subOK 4 = true := by decide +kernel

theorem fam41_sub5_ok : fam41.subOK 5 = true := by decide +kernel

theorem fam41_sub6_ok : fam41.subOK 6 = true := by decide +kernel

theorem fam41_sub7_ok : fam41.subOK 7 = true := by decide +kernel

theorem fam41_sub8_ok : fam41.subOK 8 = true := by decide +kernel

theorem fam41_sub9_ok : fam41.subOK 9 = true := by decide +kernel

theorem fam41_sub10_ok : fam41.subOK 10 = true := by decide +kernel

theorem fam41_sub11_ok : fam41.subOK 11 = true := by decide +kernel

theorem fam41_sub12_ok : fam41.subOK 12 = true := by decide +kernel

theorem fam41_sub13_ok : fam41.subOK 13 = true := by decide +kernel

theorem fam41_sub14_ok : fam41.subOK 14 = true := by decide +kernel

theorem fam41_sub15_ok : fam41.subOK 15 = true := by decide +kernel

theorem fam41_sub16_ok : fam41.subOK 16 = true := by decide +kernel

theorem fam41_sub17_ok : fam41.subOK 17 = true := by decide +kernel

theorem fam41_sub18_ok : fam41.subOK 18 = true := by decide +kernel

theorem fam41_sub19_ok : fam41.subOK 19 = true := by decide +kernel

theorem fam41_sub20_ok : fam41.subOK 20 = true := by decide +kernel

theorem fam41_sub21_ok : fam41.subOK 21 = true := by decide +kernel

theorem fam41_sub22_ok : fam41.subOK 22 = true := by decide +kernel

theorem fam41_sub23_ok : fam41.subOK 23 = true := by decide +kernel

theorem fam41_sub24_ok : fam41.subOK 24 = true := by decide +kernel

theorem fam41_sub25_ok : fam41.subOK 25 = true := by decide +kernel

theorem fam41_sub26_ok : fam41.subOK 26 = true := by decide +kernel

theorem fam41_sub27_ok : fam41.subOK 27 = true := by decide +kernel

theorem fam41_sub28_ok : fam41.subOK 28 = true := by decide +kernel

theorem fam41_sub29_ok : fam41.subOK 29 = true := by decide +kernel

theorem fam41_sub30_ok : fam41.subOK 30 = true := by decide +kernel

theorem fam41_sub31_ok : fam41.subOK 31 = true := by decide +kernel

theorem fam41_sub32_ok : fam41.subOK 32 = true := by decide +kernel

theorem fam41_sub33_ok : fam41.subOK 33 = true := by decide +kernel

theorem fam41_sub34_ok : fam41.subOK 34 = true := by decide +kernel

theorem fam41_sub35_ok : fam41.subOK 35 = true := by decide +kernel

theorem fam41_sub36_ok : fam41.subOK 36 = true := by decide +kernel

theorem fam41_sub37_ok : fam41.subOK 37 = true := by decide +kernel

theorem fam41_sub38_ok : fam41.subOK 38 = true := by decide +kernel

theorem fam41_recs : ∀ r ∈ fam41.recs, fam41.recOK r = true :=
  fam41.recs_of_chunks 11 (fun c hc => by
    interval_cases c
    exacts [fam41_recs_ok0, fam41_recs_ok1, fam41_recs_ok2, fam41_recs_ok3, fam41_recs_ok4, fam41_recs_ok5, fam41_recs_ok6, fam41_recs_ok7, fam41_recs_ok8, fam41_recs_ok9, fam41_recs_ok10])
    (by decide +kernel)

theorem fam41_subs : ∀ k < fam41.subs.length, fam41.subOK k = true := by
  intro k hk
  have h : fam41.subs.length = 39 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam41_sub0_ok, fam41_sub1_ok, fam41_sub2_ok, fam41_sub3_ok, fam41_sub4_ok, fam41_sub5_ok, fam41_sub6_ok, fam41_sub7_ok, fam41_sub8_ok, fam41_sub9_ok, fam41_sub10_ok, fam41_sub11_ok, fam41_sub12_ok, fam41_sub13_ok, fam41_sub14_ok, fam41_sub15_ok, fam41_sub16_ok, fam41_sub17_ok, fam41_sub18_ok, fam41_sub19_ok, fam41_sub20_ok, fam41_sub21_ok, fam41_sub22_ok, fam41_sub23_ok, fam41_sub24_ok, fam41_sub25_ok, fam41_sub26_ok, fam41_sub27_ok, fam41_sub28_ok, fam41_sub29_ok, fam41_sub30_ok, fam41_sub31_ok, fam41_sub32_ok, fam41_sub33_ok, fam41_sub34_ok, fam41_sub35_ok, fam41_sub36_ok, fam41_sub37_ok, fam41_sub38_ok]

end Kalai5.A16
