import Kalai5.A16.Data.Fam4
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 4. -/

namespace Kalai5.A16

theorem fam4_check : fam4.check = true := by decide +kernel

theorem fam4_recs_ok0 : fam4.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam4_recs_ok1 : fam4.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam4_recs_ok2 : fam4.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam4_recs_ok3 : fam4.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam4_recs_ok4 : fam4.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam4_recs_ok5 : fam4.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam4_recs_ok6 : fam4.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam4_recs_ok7 : fam4.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam4_recs_ok8 : fam4.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam4_recs_ok9 : fam4.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam4_recs_ok10 : fam4.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam4_sub0_ok : fam4.subOK 0 = true := by decide +kernel

theorem fam4_sub1_ok : fam4.subOK 1 = true := by decide +kernel

theorem fam4_sub2_ok : fam4.subOK 2 = true := by decide +kernel

theorem fam4_sub3_ok : fam4.subOK 3 = true := by decide +kernel

theorem fam4_sub4_ok : fam4.subOK 4 = true := by decide +kernel

theorem fam4_sub5_ok : fam4.subOK 5 = true := by decide +kernel

theorem fam4_sub6_ok : fam4.subOK 6 = true := by decide +kernel

theorem fam4_sub7_ok : fam4.subOK 7 = true := by decide +kernel

theorem fam4_sub8_ok : fam4.subOK 8 = true := by decide +kernel

theorem fam4_sub9_ok : fam4.subOK 9 = true := by decide +kernel

theorem fam4_sub10_ok : fam4.subOK 10 = true := by decide +kernel

theorem fam4_sub11_ok : fam4.subOK 11 = true := by decide +kernel

theorem fam4_sub12_ok : fam4.subOK 12 = true := by decide +kernel

theorem fam4_sub13_ok : fam4.subOK 13 = true := by decide +kernel

theorem fam4_sub14_ok : fam4.subOK 14 = true := by decide +kernel

theorem fam4_sub15_ok : fam4.subOK 15 = true := by decide +kernel

theorem fam4_sub16_ok : fam4.subOK 16 = true := by decide +kernel

theorem fam4_sub17_ok : fam4.subOK 17 = true := by decide +kernel

theorem fam4_sub18_ok : fam4.subOK 18 = true := by decide +kernel

theorem fam4_sub19_ok : fam4.subOK 19 = true := by decide +kernel

theorem fam4_sub20_ok : fam4.subOK 20 = true := by decide +kernel

theorem fam4_sub21_ok : fam4.subOK 21 = true := by decide +kernel

theorem fam4_sub22_ok : fam4.subOK 22 = true := by decide +kernel

theorem fam4_sub23_ok : fam4.subOK 23 = true := by decide +kernel

theorem fam4_sub24_ok : fam4.subOK 24 = true := by decide +kernel

theorem fam4_sub25_ok : fam4.subOK 25 = true := by decide +kernel

theorem fam4_sub26_ok : fam4.subOK 26 = true := by decide +kernel

theorem fam4_sub27_ok : fam4.subOK 27 = true := by decide +kernel

theorem fam4_recs : ∀ r ∈ fam4.recs, fam4.recOK r = true :=
  fam4.recs_of_chunks 11 (fun c hc => by
    interval_cases c
    exacts [fam4_recs_ok0, fam4_recs_ok1, fam4_recs_ok2, fam4_recs_ok3, fam4_recs_ok4, fam4_recs_ok5, fam4_recs_ok6, fam4_recs_ok7, fam4_recs_ok8, fam4_recs_ok9, fam4_recs_ok10])
    (by decide +kernel)

theorem fam4_subs : ∀ k < fam4.subs.length, fam4.subOK k = true := by
  intro k hk
  have h : fam4.subs.length = 28 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam4_sub0_ok, fam4_sub1_ok, fam4_sub2_ok, fam4_sub3_ok, fam4_sub4_ok, fam4_sub5_ok, fam4_sub6_ok, fam4_sub7_ok, fam4_sub8_ok, fam4_sub9_ok, fam4_sub10_ok, fam4_sub11_ok, fam4_sub12_ok, fam4_sub13_ok, fam4_sub14_ok, fam4_sub15_ok, fam4_sub16_ok, fam4_sub17_ok, fam4_sub18_ok, fam4_sub19_ok, fam4_sub20_ok, fam4_sub21_ok, fam4_sub22_ok, fam4_sub23_ok, fam4_sub24_ok, fam4_sub25_ok, fam4_sub26_ok, fam4_sub27_ok]

end Kalai5.A16
