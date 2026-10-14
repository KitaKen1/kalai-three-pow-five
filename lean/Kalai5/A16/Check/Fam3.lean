import Kalai5.A16.Data.Fam3
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 3. -/

namespace Kalai5.A16

theorem fam3_check : fam3.check = true := by decide +kernel

theorem fam3_recs_ok0 : fam3.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam3_recs_ok1 : fam3.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam3_recs_ok2 : fam3.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam3_recs_ok3 : fam3.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam3_recs_ok4 : fam3.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam3_recs_ok5 : fam3.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam3_recs_ok6 : fam3.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam3_recs_ok7 : fam3.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam3_recs_ok8 : fam3.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam3_recs_ok9 : fam3.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam3_sub0_ok : fam3.subOK 0 = true := by decide +kernel

theorem fam3_sub1_ok : fam3.subOK 1 = true := by decide +kernel

theorem fam3_sub2_ok : fam3.subOK 2 = true := by decide +kernel

theorem fam3_sub3_ok : fam3.subOK 3 = true := by decide +kernel

theorem fam3_sub4_ok : fam3.subOK 4 = true := by decide +kernel

theorem fam3_sub5_ok : fam3.subOK 5 = true := by decide +kernel

theorem fam3_sub6_ok : fam3.subOK 6 = true := by decide +kernel

theorem fam3_sub7_ok : fam3.subOK 7 = true := by decide +kernel

theorem fam3_sub8_ok : fam3.subOK 8 = true := by decide +kernel

theorem fam3_sub9_ok : fam3.subOK 9 = true := by decide +kernel

theorem fam3_sub10_ok : fam3.subOK 10 = true := by decide +kernel

theorem fam3_sub11_ok : fam3.subOK 11 = true := by decide +kernel

theorem fam3_sub12_ok : fam3.subOK 12 = true := by decide +kernel

theorem fam3_sub13_ok : fam3.subOK 13 = true := by decide +kernel

theorem fam3_sub14_ok : fam3.subOK 14 = true := by decide +kernel

theorem fam3_sub15_ok : fam3.subOK 15 = true := by decide +kernel

theorem fam3_sub16_ok : fam3.subOK 16 = true := by decide +kernel

theorem fam3_sub17_ok : fam3.subOK 17 = true := by decide +kernel

theorem fam3_sub18_ok : fam3.subOK 18 = true := by decide +kernel

theorem fam3_sub19_ok : fam3.subOK 19 = true := by decide +kernel

theorem fam3_sub20_ok : fam3.subOK 20 = true := by decide +kernel

theorem fam3_sub21_ok : fam3.subOK 21 = true := by decide +kernel

theorem fam3_sub22_ok : fam3.subOK 22 = true := by decide +kernel

theorem fam3_sub23_ok : fam3.subOK 23 = true := by decide +kernel

theorem fam3_sub24_ok : fam3.subOK 24 = true := by decide +kernel

theorem fam3_sub25_ok : fam3.subOK 25 = true := by decide +kernel

theorem fam3_sub26_ok : fam3.subOK 26 = true := by decide +kernel

theorem fam3_recs : ∀ r ∈ fam3.recs, fam3.recOK r = true :=
  fam3.recs_of_chunks 10 (fun c hc => by
    interval_cases c
    exacts [fam3_recs_ok0, fam3_recs_ok1, fam3_recs_ok2, fam3_recs_ok3, fam3_recs_ok4, fam3_recs_ok5, fam3_recs_ok6, fam3_recs_ok7, fam3_recs_ok8, fam3_recs_ok9])
    (by decide +kernel)

theorem fam3_subs : ∀ k < fam3.subs.length, fam3.subOK k = true := by
  intro k hk
  have h : fam3.subs.length = 27 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam3_sub0_ok, fam3_sub1_ok, fam3_sub2_ok, fam3_sub3_ok, fam3_sub4_ok, fam3_sub5_ok, fam3_sub6_ok, fam3_sub7_ok, fam3_sub8_ok, fam3_sub9_ok, fam3_sub10_ok, fam3_sub11_ok, fam3_sub12_ok, fam3_sub13_ok, fam3_sub14_ok, fam3_sub15_ok, fam3_sub16_ok, fam3_sub17_ok, fam3_sub18_ok, fam3_sub19_ok, fam3_sub20_ok, fam3_sub21_ok, fam3_sub22_ok, fam3_sub23_ok, fam3_sub24_ok, fam3_sub25_ok, fam3_sub26_ok]

end Kalai5.A16
