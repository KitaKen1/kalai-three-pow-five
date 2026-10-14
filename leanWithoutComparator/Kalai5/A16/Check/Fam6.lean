import Kalai5.A16.Data.Fam6
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 6. -/

namespace Kalai5.A16

theorem fam6_check : fam6.check = true := by decide +kernel

theorem fam6_recs_ok0 : fam6.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam6_recs_ok1 : fam6.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam6_recs_ok2 : fam6.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam6_recs_ok3 : fam6.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam6_recs_ok4 : fam6.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam6_recs_ok5 : fam6.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam6_recs_ok6 : fam6.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam6_recs_ok7 : fam6.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam6_recs_ok8 : fam6.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam6_recs_ok9 : fam6.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam6_sub0_ok : fam6.subOK 0 = true := by decide +kernel

theorem fam6_sub1_ok : fam6.subOK 1 = true := by decide +kernel

theorem fam6_sub2_ok : fam6.subOK 2 = true := by decide +kernel

theorem fam6_sub3_ok : fam6.subOK 3 = true := by decide +kernel

theorem fam6_sub4_ok : fam6.subOK 4 = true := by decide +kernel

theorem fam6_sub5_ok : fam6.subOK 5 = true := by decide +kernel

theorem fam6_sub6_ok : fam6.subOK 6 = true := by decide +kernel

theorem fam6_sub7_ok : fam6.subOK 7 = true := by decide +kernel

theorem fam6_sub8_ok : fam6.subOK 8 = true := by decide +kernel

theorem fam6_sub9_ok : fam6.subOK 9 = true := by decide +kernel

theorem fam6_sub10_ok : fam6.subOK 10 = true := by decide +kernel

theorem fam6_sub11_ok : fam6.subOK 11 = true := by decide +kernel

theorem fam6_sub12_ok : fam6.subOK 12 = true := by decide +kernel

theorem fam6_sub13_ok : fam6.subOK 13 = true := by decide +kernel

theorem fam6_sub14_ok : fam6.subOK 14 = true := by decide +kernel

theorem fam6_sub15_ok : fam6.subOK 15 = true := by decide +kernel

theorem fam6_sub16_ok : fam6.subOK 16 = true := by decide +kernel

theorem fam6_sub17_ok : fam6.subOK 17 = true := by decide +kernel

theorem fam6_sub18_ok : fam6.subOK 18 = true := by decide +kernel

theorem fam6_sub19_ok : fam6.subOK 19 = true := by decide +kernel

theorem fam6_sub20_ok : fam6.subOK 20 = true := by decide +kernel

theorem fam6_sub21_ok : fam6.subOK 21 = true := by decide +kernel

theorem fam6_sub22_ok : fam6.subOK 22 = true := by decide +kernel

theorem fam6_sub23_ok : fam6.subOK 23 = true := by decide +kernel

theorem fam6_sub24_ok : fam6.subOK 24 = true := by decide +kernel

theorem fam6_sub25_ok : fam6.subOK 25 = true := by decide +kernel

theorem fam6_sub26_ok : fam6.subOK 26 = true := by decide +kernel

theorem fam6_sub27_ok : fam6.subOK 27 = true := by decide +kernel

theorem fam6_sub28_ok : fam6.subOK 28 = true := by decide +kernel

theorem fam6_sub29_ok : fam6.subOK 29 = true := by decide +kernel

theorem fam6_sub30_ok : fam6.subOK 30 = true := by decide +kernel

theorem fam6_sub31_ok : fam6.subOK 31 = true := by decide +kernel

theorem fam6_sub32_ok : fam6.subOK 32 = true := by decide +kernel

theorem fam6_sub33_ok : fam6.subOK 33 = true := by decide +kernel

theorem fam6_sub34_ok : fam6.subOK 34 = true := by decide +kernel

theorem fam6_recs : ∀ r ∈ fam6.recs, fam6.recOK r = true :=
  fam6.recs_of_chunks 10 (fun c hc => by
    interval_cases c
    exacts [fam6_recs_ok0, fam6_recs_ok1, fam6_recs_ok2, fam6_recs_ok3, fam6_recs_ok4, fam6_recs_ok5, fam6_recs_ok6, fam6_recs_ok7, fam6_recs_ok8, fam6_recs_ok9])
    (by decide +kernel)

theorem fam6_subs : ∀ k < fam6.subs.length, fam6.subOK k = true := by
  intro k hk
  have h : fam6.subs.length = 35 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam6_sub0_ok, fam6_sub1_ok, fam6_sub2_ok, fam6_sub3_ok, fam6_sub4_ok, fam6_sub5_ok, fam6_sub6_ok, fam6_sub7_ok, fam6_sub8_ok, fam6_sub9_ok, fam6_sub10_ok, fam6_sub11_ok, fam6_sub12_ok, fam6_sub13_ok, fam6_sub14_ok, fam6_sub15_ok, fam6_sub16_ok, fam6_sub17_ok, fam6_sub18_ok, fam6_sub19_ok, fam6_sub20_ok, fam6_sub21_ok, fam6_sub22_ok, fam6_sub23_ok, fam6_sub24_ok, fam6_sub25_ok, fam6_sub26_ok, fam6_sub27_ok, fam6_sub28_ok, fam6_sub29_ok, fam6_sub30_ok, fam6_sub31_ok, fam6_sub32_ok, fam6_sub33_ok, fam6_sub34_ok]

end Kalai5.A16
