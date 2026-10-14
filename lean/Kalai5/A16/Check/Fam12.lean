import Kalai5.A16.Data.Fam12
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 12. -/

namespace Kalai5.A16

theorem fam12_check : fam12.check = true := by decide +kernel

theorem fam12_recs_ok0 : fam12.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam12_recs_ok1 : fam12.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam12_recs_ok2 : fam12.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam12_recs_ok3 : fam12.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam12_recs_ok4 : fam12.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam12_recs_ok5 : fam12.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam12_recs_ok6 : fam12.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam12_recs_ok7 : fam12.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam12_recs_ok8 : fam12.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam12_recs_ok9 : fam12.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam12_recs_ok10 : fam12.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam12_recs_ok11 : fam12.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam12_recs_ok12 : fam12.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam12_recs_ok13 : fam12.recsOK (40 * 13) 40 = true := by decide +kernel

theorem fam12_recs_ok14 : fam12.recsOK (40 * 14) 40 = true := by decide +kernel

theorem fam12_sub0_ok : fam12.subOK 0 = true := by decide +kernel

theorem fam12_sub1_ok : fam12.subOK 1 = true := by decide +kernel

theorem fam12_sub2_ok : fam12.subOK 2 = true := by decide +kernel

theorem fam12_sub3_ok : fam12.subOK 3 = true := by decide +kernel

theorem fam12_sub4_ok : fam12.subOK 4 = true := by decide +kernel

theorem fam12_sub5_ok : fam12.subOK 5 = true := by decide +kernel

theorem fam12_sub6_ok : fam12.subOK 6 = true := by decide +kernel

theorem fam12_sub7_ok : fam12.subOK 7 = true := by decide +kernel

theorem fam12_sub8_ok : fam12.subOK 8 = true := by decide +kernel

theorem fam12_sub9_ok : fam12.subOK 9 = true := by decide +kernel

theorem fam12_sub10_ok : fam12.subOK 10 = true := by decide +kernel

theorem fam12_sub11_ok : fam12.subOK 11 = true := by decide +kernel

theorem fam12_sub12_ok : fam12.subOK 12 = true := by decide +kernel

theorem fam12_sub13_ok : fam12.subOK 13 = true := by decide +kernel

theorem fam12_sub14_ok : fam12.subOK 14 = true := by decide +kernel

theorem fam12_sub15_ok : fam12.subOK 15 = true := by decide +kernel

theorem fam12_sub16_ok : fam12.subOK 16 = true := by decide +kernel

theorem fam12_sub17_ok : fam12.subOK 17 = true := by decide +kernel

theorem fam12_sub18_ok : fam12.subOK 18 = true := by decide +kernel

theorem fam12_sub19_ok : fam12.subOK 19 = true := by decide +kernel

theorem fam12_sub20_ok : fam12.subOK 20 = true := by decide +kernel

theorem fam12_sub21_ok : fam12.subOK 21 = true := by decide +kernel

theorem fam12_sub22_ok : fam12.subOK 22 = true := by decide +kernel

theorem fam12_sub23_ok : fam12.subOK 23 = true := by decide +kernel

theorem fam12_sub24_ok : fam12.subOK 24 = true := by decide +kernel

theorem fam12_sub25_ok : fam12.subOK 25 = true := by decide +kernel

theorem fam12_sub26_ok : fam12.subOK 26 = true := by decide +kernel

theorem fam12_sub27_ok : fam12.subOK 27 = true := by decide +kernel

theorem fam12_sub28_ok : fam12.subOK 28 = true := by decide +kernel

theorem fam12_sub29_ok : fam12.subOK 29 = true := by decide +kernel

theorem fam12_sub30_ok : fam12.subOK 30 = true := by decide +kernel

theorem fam12_sub31_ok : fam12.subOK 31 = true := by decide +kernel

theorem fam12_recs : ∀ r ∈ fam12.recs, fam12.recOK r = true :=
  fam12.recs_of_chunks 15 (fun c hc => by
    interval_cases c
    exacts [fam12_recs_ok0, fam12_recs_ok1, fam12_recs_ok2, fam12_recs_ok3, fam12_recs_ok4, fam12_recs_ok5, fam12_recs_ok6, fam12_recs_ok7, fam12_recs_ok8, fam12_recs_ok9, fam12_recs_ok10, fam12_recs_ok11, fam12_recs_ok12, fam12_recs_ok13, fam12_recs_ok14])
    (by decide +kernel)

theorem fam12_subs : ∀ k < fam12.subs.length, fam12.subOK k = true := by
  intro k hk
  have h : fam12.subs.length = 32 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam12_sub0_ok, fam12_sub1_ok, fam12_sub2_ok, fam12_sub3_ok, fam12_sub4_ok, fam12_sub5_ok, fam12_sub6_ok, fam12_sub7_ok, fam12_sub8_ok, fam12_sub9_ok, fam12_sub10_ok, fam12_sub11_ok, fam12_sub12_ok, fam12_sub13_ok, fam12_sub14_ok, fam12_sub15_ok, fam12_sub16_ok, fam12_sub17_ok, fam12_sub18_ok, fam12_sub19_ok, fam12_sub20_ok, fam12_sub21_ok, fam12_sub22_ok, fam12_sub23_ok, fam12_sub24_ok, fam12_sub25_ok, fam12_sub26_ok, fam12_sub27_ok, fam12_sub28_ok, fam12_sub29_ok, fam12_sub30_ok, fam12_sub31_ok]

end Kalai5.A16
