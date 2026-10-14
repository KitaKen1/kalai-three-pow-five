import Kalai5.A16.Data.Fam10
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 10. -/

namespace Kalai5.A16

theorem fam10_check : fam10.check = true := by decide +kernel

theorem fam10_recs_ok0 : fam10.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam10_recs_ok1 : fam10.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam10_recs_ok2 : fam10.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam10_recs_ok3 : fam10.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam10_recs_ok4 : fam10.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam10_recs_ok5 : fam10.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam10_recs_ok6 : fam10.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam10_recs_ok7 : fam10.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam10_recs_ok8 : fam10.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam10_recs_ok9 : fam10.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam10_recs_ok10 : fam10.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam10_recs_ok11 : fam10.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam10_sub0_ok : fam10.subOK 0 = true := by decide +kernel

theorem fam10_sub1_ok : fam10.subOK 1 = true := by decide +kernel

theorem fam10_sub2_ok : fam10.subOK 2 = true := by decide +kernel

theorem fam10_sub3_ok : fam10.subOK 3 = true := by decide +kernel

theorem fam10_sub4_ok : fam10.subOK 4 = true := by decide +kernel

theorem fam10_sub5_ok : fam10.subOK 5 = true := by decide +kernel

theorem fam10_sub6_ok : fam10.subOK 6 = true := by decide +kernel

theorem fam10_sub7_ok : fam10.subOK 7 = true := by decide +kernel

theorem fam10_sub8_ok : fam10.subOK 8 = true := by decide +kernel

theorem fam10_sub9_ok : fam10.subOK 9 = true := by decide +kernel

theorem fam10_sub10_ok : fam10.subOK 10 = true := by decide +kernel

theorem fam10_sub11_ok : fam10.subOK 11 = true := by decide +kernel

theorem fam10_sub12_ok : fam10.subOK 12 = true := by decide +kernel

theorem fam10_sub13_ok : fam10.subOK 13 = true := by decide +kernel

theorem fam10_sub14_ok : fam10.subOK 14 = true := by decide +kernel

theorem fam10_sub15_ok : fam10.subOK 15 = true := by decide +kernel

theorem fam10_sub16_ok : fam10.subOK 16 = true := by decide +kernel

theorem fam10_sub17_ok : fam10.subOK 17 = true := by decide +kernel

theorem fam10_sub18_ok : fam10.subOK 18 = true := by decide +kernel

theorem fam10_sub19_ok : fam10.subOK 19 = true := by decide +kernel

theorem fam10_sub20_ok : fam10.subOK 20 = true := by decide +kernel

theorem fam10_sub21_ok : fam10.subOK 21 = true := by decide +kernel

theorem fam10_sub22_ok : fam10.subOK 22 = true := by decide +kernel

theorem fam10_sub23_ok : fam10.subOK 23 = true := by decide +kernel

theorem fam10_sub24_ok : fam10.subOK 24 = true := by decide +kernel

theorem fam10_sub25_ok : fam10.subOK 25 = true := by decide +kernel

theorem fam10_sub26_ok : fam10.subOK 26 = true := by decide +kernel

theorem fam10_sub27_ok : fam10.subOK 27 = true := by decide +kernel

theorem fam10_sub28_ok : fam10.subOK 28 = true := by decide +kernel

theorem fam10_sub29_ok : fam10.subOK 29 = true := by decide +kernel

theorem fam10_recs : ∀ r ∈ fam10.recs, fam10.recOK r = true :=
  fam10.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [fam10_recs_ok0, fam10_recs_ok1, fam10_recs_ok2, fam10_recs_ok3, fam10_recs_ok4, fam10_recs_ok5, fam10_recs_ok6, fam10_recs_ok7, fam10_recs_ok8, fam10_recs_ok9, fam10_recs_ok10, fam10_recs_ok11])
    (by decide +kernel)

theorem fam10_subs : ∀ k < fam10.subs.length, fam10.subOK k = true := by
  intro k hk
  have h : fam10.subs.length = 30 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam10_sub0_ok, fam10_sub1_ok, fam10_sub2_ok, fam10_sub3_ok, fam10_sub4_ok, fam10_sub5_ok, fam10_sub6_ok, fam10_sub7_ok, fam10_sub8_ok, fam10_sub9_ok, fam10_sub10_ok, fam10_sub11_ok, fam10_sub12_ok, fam10_sub13_ok, fam10_sub14_ok, fam10_sub15_ok, fam10_sub16_ok, fam10_sub17_ok, fam10_sub18_ok, fam10_sub19_ok, fam10_sub20_ok, fam10_sub21_ok, fam10_sub22_ok, fam10_sub23_ok, fam10_sub24_ok, fam10_sub25_ok, fam10_sub26_ok, fam10_sub27_ok, fam10_sub28_ok, fam10_sub29_ok]

end Kalai5.A16
