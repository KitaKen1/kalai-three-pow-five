import Kalai5.A16.Data.Fam2
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 2. -/

namespace Kalai5.A16

theorem fam2_check : fam2.check = true := by decide +kernel

theorem fam2_recs_ok0 : fam2.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam2_recs_ok1 : fam2.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam2_recs_ok2 : fam2.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam2_recs_ok3 : fam2.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam2_recs_ok4 : fam2.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam2_recs_ok5 : fam2.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam2_recs_ok6 : fam2.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam2_recs_ok7 : fam2.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam2_sub0_ok : fam2.subOK 0 = true := by decide +kernel

theorem fam2_sub1_ok : fam2.subOK 1 = true := by decide +kernel

theorem fam2_sub2_ok : fam2.subOK 2 = true := by decide +kernel

theorem fam2_sub3_ok : fam2.subOK 3 = true := by decide +kernel

theorem fam2_sub4_ok : fam2.subOK 4 = true := by decide +kernel

theorem fam2_sub5_ok : fam2.subOK 5 = true := by decide +kernel

theorem fam2_sub6_ok : fam2.subOK 6 = true := by decide +kernel

theorem fam2_sub7_ok : fam2.subOK 7 = true := by decide +kernel

theorem fam2_sub8_ok : fam2.subOK 8 = true := by decide +kernel

theorem fam2_sub9_ok : fam2.subOK 9 = true := by decide +kernel

theorem fam2_sub10_ok : fam2.subOK 10 = true := by decide +kernel

theorem fam2_sub11_ok : fam2.subOK 11 = true := by decide +kernel

theorem fam2_sub12_ok : fam2.subOK 12 = true := by decide +kernel

theorem fam2_sub13_ok : fam2.subOK 13 = true := by decide +kernel

theorem fam2_sub14_ok : fam2.subOK 14 = true := by decide +kernel

theorem fam2_sub15_ok : fam2.subOK 15 = true := by decide +kernel

theorem fam2_sub16_ok : fam2.subOK 16 = true := by decide +kernel

theorem fam2_sub17_ok : fam2.subOK 17 = true := by decide +kernel

theorem fam2_sub18_ok : fam2.subOK 18 = true := by decide +kernel

theorem fam2_sub19_ok : fam2.subOK 19 = true := by decide +kernel

theorem fam2_sub20_ok : fam2.subOK 20 = true := by decide +kernel

theorem fam2_sub21_ok : fam2.subOK 21 = true := by decide +kernel

theorem fam2_recs : ∀ r ∈ fam2.recs, fam2.recOK r = true :=
  fam2.recs_of_chunks 8 (fun c hc => by
    interval_cases c
    exacts [fam2_recs_ok0, fam2_recs_ok1, fam2_recs_ok2, fam2_recs_ok3, fam2_recs_ok4, fam2_recs_ok5, fam2_recs_ok6, fam2_recs_ok7])
    (by decide +kernel)

theorem fam2_subs : ∀ k < fam2.subs.length, fam2.subOK k = true := by
  intro k hk
  have h : fam2.subs.length = 22 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam2_sub0_ok, fam2_sub1_ok, fam2_sub2_ok, fam2_sub3_ok, fam2_sub4_ok, fam2_sub5_ok, fam2_sub6_ok, fam2_sub7_ok, fam2_sub8_ok, fam2_sub9_ok, fam2_sub10_ok, fam2_sub11_ok, fam2_sub12_ok, fam2_sub13_ok, fam2_sub14_ok, fam2_sub15_ok, fam2_sub16_ok, fam2_sub17_ok, fam2_sub18_ok, fam2_sub19_ok, fam2_sub20_ok, fam2_sub21_ok]

end Kalai5.A16
