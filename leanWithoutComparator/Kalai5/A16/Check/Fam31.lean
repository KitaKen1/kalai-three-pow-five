import Kalai5.A16.Data.Fam31
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 31. -/

namespace Kalai5.A16

theorem fam31_check : fam31.check = true := by decide +kernel

theorem fam31_recs_ok0 : fam31.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam31_recs_ok1 : fam31.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam31_recs_ok2 : fam31.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam31_recs_ok3 : fam31.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam31_recs_ok4 : fam31.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam31_recs_ok5 : fam31.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam31_recs_ok6 : fam31.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam31_recs_ok7 : fam31.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam31_recs_ok8 : fam31.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam31_recs_ok9 : fam31.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam31_recs_ok10 : fam31.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam31_recs_ok11 : fam31.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam31_recs_ok12 : fam31.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam31_sub0_ok : fam31.subOK 0 = true := by decide +kernel

theorem fam31_sub1_ok : fam31.subOK 1 = true := by decide +kernel

theorem fam31_sub2_ok : fam31.subOK 2 = true := by decide +kernel

theorem fam31_sub3_ok : fam31.subOK 3 = true := by decide +kernel

theorem fam31_sub4_ok : fam31.subOK 4 = true := by decide +kernel

theorem fam31_sub5_ok : fam31.subOK 5 = true := by decide +kernel

theorem fam31_sub6_ok : fam31.subOK 6 = true := by decide +kernel

theorem fam31_sub7_ok : fam31.subOK 7 = true := by decide +kernel

theorem fam31_sub8_ok : fam31.subOK 8 = true := by decide +kernel

theorem fam31_sub9_ok : fam31.subOK 9 = true := by decide +kernel

theorem fam31_sub10_ok : fam31.subOK 10 = true := by decide +kernel

theorem fam31_sub11_ok : fam31.subOK 11 = true := by decide +kernel

theorem fam31_sub12_ok : fam31.subOK 12 = true := by decide +kernel

theorem fam31_sub13_ok : fam31.subOK 13 = true := by decide +kernel

theorem fam31_sub14_ok : fam31.subOK 14 = true := by decide +kernel

theorem fam31_sub15_ok : fam31.subOK 15 = true := by decide +kernel

theorem fam31_sub16_ok : fam31.subOK 16 = true := by decide +kernel

theorem fam31_sub17_ok : fam31.subOK 17 = true := by decide +kernel

theorem fam31_sub18_ok : fam31.subOK 18 = true := by decide +kernel

theorem fam31_sub19_ok : fam31.subOK 19 = true := by decide +kernel

theorem fam31_sub20_ok : fam31.subOK 20 = true := by decide +kernel

theorem fam31_sub21_ok : fam31.subOK 21 = true := by decide +kernel

theorem fam31_sub22_ok : fam31.subOK 22 = true := by decide +kernel

theorem fam31_sub23_ok : fam31.subOK 23 = true := by decide +kernel

theorem fam31_sub24_ok : fam31.subOK 24 = true := by decide +kernel

theorem fam31_sub25_ok : fam31.subOK 25 = true := by decide +kernel

theorem fam31_sub26_ok : fam31.subOK 26 = true := by decide +kernel

theorem fam31_sub27_ok : fam31.subOK 27 = true := by decide +kernel

theorem fam31_sub28_ok : fam31.subOK 28 = true := by decide +kernel

theorem fam31_sub29_ok : fam31.subOK 29 = true := by decide +kernel

theorem fam31_sub30_ok : fam31.subOK 30 = true := by decide +kernel

theorem fam31_sub31_ok : fam31.subOK 31 = true := by decide +kernel

theorem fam31_sub32_ok : fam31.subOK 32 = true := by decide +kernel

theorem fam31_sub33_ok : fam31.subOK 33 = true := by decide +kernel

theorem fam31_sub34_ok : fam31.subOK 34 = true := by decide +kernel

theorem fam31_recs : ∀ r ∈ fam31.recs, fam31.recOK r = true :=
  fam31.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [fam31_recs_ok0, fam31_recs_ok1, fam31_recs_ok2, fam31_recs_ok3, fam31_recs_ok4, fam31_recs_ok5, fam31_recs_ok6, fam31_recs_ok7, fam31_recs_ok8, fam31_recs_ok9, fam31_recs_ok10, fam31_recs_ok11, fam31_recs_ok12])
    (by decide +kernel)

theorem fam31_subs : ∀ k < fam31.subs.length, fam31.subOK k = true := by
  intro k hk
  have h : fam31.subs.length = 35 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam31_sub0_ok, fam31_sub1_ok, fam31_sub2_ok, fam31_sub3_ok, fam31_sub4_ok, fam31_sub5_ok, fam31_sub6_ok, fam31_sub7_ok, fam31_sub8_ok, fam31_sub9_ok, fam31_sub10_ok, fam31_sub11_ok, fam31_sub12_ok, fam31_sub13_ok, fam31_sub14_ok, fam31_sub15_ok, fam31_sub16_ok, fam31_sub17_ok, fam31_sub18_ok, fam31_sub19_ok, fam31_sub20_ok, fam31_sub21_ok, fam31_sub22_ok, fam31_sub23_ok, fam31_sub24_ok, fam31_sub25_ok, fam31_sub26_ok, fam31_sub27_ok, fam31_sub28_ok, fam31_sub29_ok, fam31_sub30_ok, fam31_sub31_ok, fam31_sub32_ok, fam31_sub33_ok, fam31_sub34_ok]

end Kalai5.A16
