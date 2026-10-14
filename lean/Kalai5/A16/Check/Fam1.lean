import Kalai5.A16.Data.Fam1
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 1. -/

namespace Kalai5.A16

theorem fam1_check : fam1.check = true := by decide +kernel

theorem fam1_recs_ok0 : fam1.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam1_recs_ok1 : fam1.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam1_recs_ok2 : fam1.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam1_recs_ok3 : fam1.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam1_recs_ok4 : fam1.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam1_recs_ok5 : fam1.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam1_recs_ok6 : fam1.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam1_recs_ok7 : fam1.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam1_sub0_ok : fam1.subOK 0 = true := by decide +kernel

theorem fam1_sub1_ok : fam1.subOK 1 = true := by decide +kernel

theorem fam1_sub2_ok : fam1.subOK 2 = true := by decide +kernel

theorem fam1_sub3_ok : fam1.subOK 3 = true := by decide +kernel

theorem fam1_sub4_ok : fam1.subOK 4 = true := by decide +kernel

theorem fam1_sub5_ok : fam1.subOK 5 = true := by decide +kernel

theorem fam1_sub6_ok : fam1.subOK 6 = true := by decide +kernel

theorem fam1_sub7_ok : fam1.subOK 7 = true := by decide +kernel

theorem fam1_sub8_ok : fam1.subOK 8 = true := by decide +kernel

theorem fam1_sub9_ok : fam1.subOK 9 = true := by decide +kernel

theorem fam1_sub10_ok : fam1.subOK 10 = true := by decide +kernel

theorem fam1_sub11_ok : fam1.subOK 11 = true := by decide +kernel

theorem fam1_sub12_ok : fam1.subOK 12 = true := by decide +kernel

theorem fam1_sub13_ok : fam1.subOK 13 = true := by decide +kernel

theorem fam1_sub14_ok : fam1.subOK 14 = true := by decide +kernel

theorem fam1_sub15_ok : fam1.subOK 15 = true := by decide +kernel

theorem fam1_sub16_ok : fam1.subOK 16 = true := by decide +kernel

theorem fam1_sub17_ok : fam1.subOK 17 = true := by decide +kernel

theorem fam1_sub18_ok : fam1.subOK 18 = true := by decide +kernel

theorem fam1_sub19_ok : fam1.subOK 19 = true := by decide +kernel

theorem fam1_recs : ∀ r ∈ fam1.recs, fam1.recOK r = true :=
  fam1.recs_of_chunks 8 (fun c hc => by
    interval_cases c
    exacts [fam1_recs_ok0, fam1_recs_ok1, fam1_recs_ok2, fam1_recs_ok3, fam1_recs_ok4, fam1_recs_ok5, fam1_recs_ok6, fam1_recs_ok7])
    (by decide +kernel)

theorem fam1_subs : ∀ k < fam1.subs.length, fam1.subOK k = true := by
  intro k hk
  have h : fam1.subs.length = 20 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam1_sub0_ok, fam1_sub1_ok, fam1_sub2_ok, fam1_sub3_ok, fam1_sub4_ok, fam1_sub5_ok, fam1_sub6_ok, fam1_sub7_ok, fam1_sub8_ok, fam1_sub9_ok, fam1_sub10_ok, fam1_sub11_ok, fam1_sub12_ok, fam1_sub13_ok, fam1_sub14_ok, fam1_sub15_ok, fam1_sub16_ok, fam1_sub17_ok, fam1_sub18_ok, fam1_sub19_ok]

end Kalai5.A16
