import Kalai5.A16.Data.Fam38
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 38. -/

namespace Kalai5.A16

theorem fam38_check : fam38.check = true := by decide +kernel

theorem fam38_recs_ok0 : fam38.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam38_recs_ok1 : fam38.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam38_recs_ok2 : fam38.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam38_recs_ok3 : fam38.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam38_recs_ok4 : fam38.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam38_recs_ok5 : fam38.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam38_recs_ok6 : fam38.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam38_recs_ok7 : fam38.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam38_recs_ok8 : fam38.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam38_recs_ok9 : fam38.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam38_recs_ok10 : fam38.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam38_recs_ok11 : fam38.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam38_sub0_ok : fam38.subOK 0 = true := by decide +kernel

theorem fam38_sub1_ok : fam38.subOK 1 = true := by decide +kernel

theorem fam38_sub2_ok : fam38.subOK 2 = true := by decide +kernel

theorem fam38_sub3_ok : fam38.subOK 3 = true := by decide +kernel

theorem fam38_sub4_ok : fam38.subOK 4 = true := by decide +kernel

theorem fam38_sub5_ok : fam38.subOK 5 = true := by decide +kernel

theorem fam38_sub6_ok : fam38.subOK 6 = true := by decide +kernel

theorem fam38_sub7_ok : fam38.subOK 7 = true := by decide +kernel

theorem fam38_sub8_ok : fam38.subOK 8 = true := by decide +kernel

theorem fam38_sub9_ok : fam38.subOK 9 = true := by decide +kernel

theorem fam38_sub10_ok : fam38.subOK 10 = true := by decide +kernel

theorem fam38_sub11_ok : fam38.subOK 11 = true := by decide +kernel

theorem fam38_sub12_ok : fam38.subOK 12 = true := by decide +kernel

theorem fam38_sub13_ok : fam38.subOK 13 = true := by decide +kernel

theorem fam38_sub14_ok : fam38.subOK 14 = true := by decide +kernel

theorem fam38_sub15_ok : fam38.subOK 15 = true := by decide +kernel

theorem fam38_sub16_ok : fam38.subOK 16 = true := by decide +kernel

theorem fam38_sub17_ok : fam38.subOK 17 = true := by decide +kernel

theorem fam38_sub18_ok : fam38.subOK 18 = true := by decide +kernel

theorem fam38_sub19_ok : fam38.subOK 19 = true := by decide +kernel

theorem fam38_sub20_ok : fam38.subOK 20 = true := by decide +kernel

theorem fam38_sub21_ok : fam38.subOK 21 = true := by decide +kernel

theorem fam38_sub22_ok : fam38.subOK 22 = true := by decide +kernel

theorem fam38_sub23_ok : fam38.subOK 23 = true := by decide +kernel

theorem fam38_sub24_ok : fam38.subOK 24 = true := by decide +kernel

theorem fam38_sub25_ok : fam38.subOK 25 = true := by decide +kernel

theorem fam38_sub26_ok : fam38.subOK 26 = true := by decide +kernel

theorem fam38_sub27_ok : fam38.subOK 27 = true := by decide +kernel

theorem fam38_sub28_ok : fam38.subOK 28 = true := by decide +kernel

theorem fam38_sub29_ok : fam38.subOK 29 = true := by decide +kernel

theorem fam38_sub30_ok : fam38.subOK 30 = true := by decide +kernel

theorem fam38_sub31_ok : fam38.subOK 31 = true := by decide +kernel

theorem fam38_sub32_ok : fam38.subOK 32 = true := by decide +kernel

theorem fam38_sub33_ok : fam38.subOK 33 = true := by decide +kernel

theorem fam38_recs : ∀ r ∈ fam38.recs, fam38.recOK r = true :=
  fam38.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [fam38_recs_ok0, fam38_recs_ok1, fam38_recs_ok2, fam38_recs_ok3, fam38_recs_ok4, fam38_recs_ok5, fam38_recs_ok6, fam38_recs_ok7, fam38_recs_ok8, fam38_recs_ok9, fam38_recs_ok10, fam38_recs_ok11])
    (by decide +kernel)

theorem fam38_subs : ∀ k < fam38.subs.length, fam38.subOK k = true := by
  intro k hk
  have h : fam38.subs.length = 34 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam38_sub0_ok, fam38_sub1_ok, fam38_sub2_ok, fam38_sub3_ok, fam38_sub4_ok, fam38_sub5_ok, fam38_sub6_ok, fam38_sub7_ok, fam38_sub8_ok, fam38_sub9_ok, fam38_sub10_ok, fam38_sub11_ok, fam38_sub12_ok, fam38_sub13_ok, fam38_sub14_ok, fam38_sub15_ok, fam38_sub16_ok, fam38_sub17_ok, fam38_sub18_ok, fam38_sub19_ok, fam38_sub20_ok, fam38_sub21_ok, fam38_sub22_ok, fam38_sub23_ok, fam38_sub24_ok, fam38_sub25_ok, fam38_sub26_ok, fam38_sub27_ok, fam38_sub28_ok, fam38_sub29_ok, fam38_sub30_ok, fam38_sub31_ok, fam38_sub32_ok, fam38_sub33_ok]

end Kalai5.A16
