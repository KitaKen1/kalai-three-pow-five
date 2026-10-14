import Kalai5.A16.Data.Fam11
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 11. -/

namespace Kalai5.A16

theorem fam11_check : fam11.check = true := by decide +kernel

theorem fam11_recs_ok0 : fam11.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam11_recs_ok1 : fam11.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam11_recs_ok2 : fam11.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam11_recs_ok3 : fam11.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam11_recs_ok4 : fam11.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam11_recs_ok5 : fam11.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam11_recs_ok6 : fam11.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam11_recs_ok7 : fam11.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam11_recs_ok8 : fam11.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam11_recs_ok9 : fam11.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam11_recs_ok10 : fam11.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam11_recs_ok11 : fam11.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam11_recs_ok12 : fam11.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam11_sub0_ok : fam11.subOK 0 = true := by decide +kernel

theorem fam11_sub1_ok : fam11.subOK 1 = true := by decide +kernel

theorem fam11_sub2_ok : fam11.subOK 2 = true := by decide +kernel

theorem fam11_sub3_ok : fam11.subOK 3 = true := by decide +kernel

theorem fam11_sub4_ok : fam11.subOK 4 = true := by decide +kernel

theorem fam11_sub5_ok : fam11.subOK 5 = true := by decide +kernel

theorem fam11_sub6_ok : fam11.subOK 6 = true := by decide +kernel

theorem fam11_sub7_ok : fam11.subOK 7 = true := by decide +kernel

theorem fam11_sub8_ok : fam11.subOK 8 = true := by decide +kernel

theorem fam11_sub9_ok : fam11.subOK 9 = true := by decide +kernel

theorem fam11_sub10_ok : fam11.subOK 10 = true := by decide +kernel

theorem fam11_sub11_ok : fam11.subOK 11 = true := by decide +kernel

theorem fam11_sub12_ok : fam11.subOK 12 = true := by decide +kernel

theorem fam11_sub13_ok : fam11.subOK 13 = true := by decide +kernel

theorem fam11_sub14_ok : fam11.subOK 14 = true := by decide +kernel

theorem fam11_sub15_ok : fam11.subOK 15 = true := by decide +kernel

theorem fam11_sub16_ok : fam11.subOK 16 = true := by decide +kernel

theorem fam11_sub17_ok : fam11.subOK 17 = true := by decide +kernel

theorem fam11_sub18_ok : fam11.subOK 18 = true := by decide +kernel

theorem fam11_sub19_ok : fam11.subOK 19 = true := by decide +kernel

theorem fam11_sub20_ok : fam11.subOK 20 = true := by decide +kernel

theorem fam11_sub21_ok : fam11.subOK 21 = true := by decide +kernel

theorem fam11_sub22_ok : fam11.subOK 22 = true := by decide +kernel

theorem fam11_sub23_ok : fam11.subOK 23 = true := by decide +kernel

theorem fam11_sub24_ok : fam11.subOK 24 = true := by decide +kernel

theorem fam11_sub25_ok : fam11.subOK 25 = true := by decide +kernel

theorem fam11_sub26_ok : fam11.subOK 26 = true := by decide +kernel

theorem fam11_sub27_ok : fam11.subOK 27 = true := by decide +kernel

theorem fam11_sub28_ok : fam11.subOK 28 = true := by decide +kernel

theorem fam11_sub29_ok : fam11.subOK 29 = true := by decide +kernel

theorem fam11_recs : ∀ r ∈ fam11.recs, fam11.recOK r = true :=
  fam11.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [fam11_recs_ok0, fam11_recs_ok1, fam11_recs_ok2, fam11_recs_ok3, fam11_recs_ok4, fam11_recs_ok5, fam11_recs_ok6, fam11_recs_ok7, fam11_recs_ok8, fam11_recs_ok9, fam11_recs_ok10, fam11_recs_ok11, fam11_recs_ok12])
    (by decide +kernel)

theorem fam11_subs : ∀ k < fam11.subs.length, fam11.subOK k = true := by
  intro k hk
  have h : fam11.subs.length = 30 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam11_sub0_ok, fam11_sub1_ok, fam11_sub2_ok, fam11_sub3_ok, fam11_sub4_ok, fam11_sub5_ok, fam11_sub6_ok, fam11_sub7_ok, fam11_sub8_ok, fam11_sub9_ok, fam11_sub10_ok, fam11_sub11_ok, fam11_sub12_ok, fam11_sub13_ok, fam11_sub14_ok, fam11_sub15_ok, fam11_sub16_ok, fam11_sub17_ok, fam11_sub18_ok, fam11_sub19_ok, fam11_sub20_ok, fam11_sub21_ok, fam11_sub22_ok, fam11_sub23_ok, fam11_sub24_ok, fam11_sub25_ok, fam11_sub26_ok, fam11_sub27_ok, fam11_sub28_ok, fam11_sub29_ok]

end Kalai5.A16
