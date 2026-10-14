import Kalai5.A16.Data.Fam30
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 30. -/

namespace Kalai5.A16

theorem fam30_check : fam30.check = true := by decide +kernel

theorem fam30_recs_ok0 : fam30.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam30_recs_ok1 : fam30.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam30_recs_ok2 : fam30.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam30_recs_ok3 : fam30.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam30_recs_ok4 : fam30.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam30_recs_ok5 : fam30.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam30_recs_ok6 : fam30.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam30_recs_ok7 : fam30.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam30_recs_ok8 : fam30.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam30_recs_ok9 : fam30.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam30_recs_ok10 : fam30.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam30_sub0_ok : fam30.subOK 0 = true := by decide +kernel

theorem fam30_sub1_ok : fam30.subOK 1 = true := by decide +kernel

theorem fam30_sub2_ok : fam30.subOK 2 = true := by decide +kernel

theorem fam30_sub3_ok : fam30.subOK 3 = true := by decide +kernel

theorem fam30_sub4_ok : fam30.subOK 4 = true := by decide +kernel

theorem fam30_sub5_ok : fam30.subOK 5 = true := by decide +kernel

theorem fam30_sub6_ok : fam30.subOK 6 = true := by decide +kernel

theorem fam30_sub7_ok : fam30.subOK 7 = true := by decide +kernel

theorem fam30_sub8_ok : fam30.subOK 8 = true := by decide +kernel

theorem fam30_sub9_ok : fam30.subOK 9 = true := by decide +kernel

theorem fam30_sub10_ok : fam30.subOK 10 = true := by decide +kernel

theorem fam30_sub11_ok : fam30.subOK 11 = true := by decide +kernel

theorem fam30_sub12_ok : fam30.subOK 12 = true := by decide +kernel

theorem fam30_sub13_ok : fam30.subOK 13 = true := by decide +kernel

theorem fam30_sub14_ok : fam30.subOK 14 = true := by decide +kernel

theorem fam30_sub15_ok : fam30.subOK 15 = true := by decide +kernel

theorem fam30_sub16_ok : fam30.subOK 16 = true := by decide +kernel

theorem fam30_sub17_ok : fam30.subOK 17 = true := by decide +kernel

theorem fam30_sub18_ok : fam30.subOK 18 = true := by decide +kernel

theorem fam30_sub19_ok : fam30.subOK 19 = true := by decide +kernel

theorem fam30_sub20_ok : fam30.subOK 20 = true := by decide +kernel

theorem fam30_sub21_ok : fam30.subOK 21 = true := by decide +kernel

theorem fam30_sub22_ok : fam30.subOK 22 = true := by decide +kernel

theorem fam30_sub23_ok : fam30.subOK 23 = true := by decide +kernel

theorem fam30_sub24_ok : fam30.subOK 24 = true := by decide +kernel

theorem fam30_sub25_ok : fam30.subOK 25 = true := by decide +kernel

theorem fam30_sub26_ok : fam30.subOK 26 = true := by decide +kernel

theorem fam30_sub27_ok : fam30.subOK 27 = true := by decide +kernel

theorem fam30_sub28_ok : fam30.subOK 28 = true := by decide +kernel

theorem fam30_sub29_ok : fam30.subOK 29 = true := by decide +kernel

theorem fam30_sub30_ok : fam30.subOK 30 = true := by decide +kernel

theorem fam30_sub31_ok : fam30.subOK 31 = true := by decide +kernel

theorem fam30_sub32_ok : fam30.subOK 32 = true := by decide +kernel

theorem fam30_recs : ∀ r ∈ fam30.recs, fam30.recOK r = true :=
  fam30.recs_of_chunks 11 (fun c hc => by
    interval_cases c
    exacts [fam30_recs_ok0, fam30_recs_ok1, fam30_recs_ok2, fam30_recs_ok3, fam30_recs_ok4, fam30_recs_ok5, fam30_recs_ok6, fam30_recs_ok7, fam30_recs_ok8, fam30_recs_ok9, fam30_recs_ok10])
    (by decide +kernel)

theorem fam30_subs : ∀ k < fam30.subs.length, fam30.subOK k = true := by
  intro k hk
  have h : fam30.subs.length = 33 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam30_sub0_ok, fam30_sub1_ok, fam30_sub2_ok, fam30_sub3_ok, fam30_sub4_ok, fam30_sub5_ok, fam30_sub6_ok, fam30_sub7_ok, fam30_sub8_ok, fam30_sub9_ok, fam30_sub10_ok, fam30_sub11_ok, fam30_sub12_ok, fam30_sub13_ok, fam30_sub14_ok, fam30_sub15_ok, fam30_sub16_ok, fam30_sub17_ok, fam30_sub18_ok, fam30_sub19_ok, fam30_sub20_ok, fam30_sub21_ok, fam30_sub22_ok, fam30_sub23_ok, fam30_sub24_ok, fam30_sub25_ok, fam30_sub26_ok, fam30_sub27_ok, fam30_sub28_ok, fam30_sub29_ok, fam30_sub30_ok, fam30_sub31_ok, fam30_sub32_ok]

end Kalai5.A16
