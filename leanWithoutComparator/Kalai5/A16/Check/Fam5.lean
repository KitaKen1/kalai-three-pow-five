import Kalai5.A16.Data.Fam5
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 5. -/

namespace Kalai5.A16

theorem fam5_check : fam5.check = true := by decide +kernel

theorem fam5_recs_ok0 : fam5.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam5_recs_ok1 : fam5.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam5_recs_ok2 : fam5.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam5_recs_ok3 : fam5.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam5_recs_ok4 : fam5.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam5_recs_ok5 : fam5.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam5_recs_ok6 : fam5.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam5_recs_ok7 : fam5.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam5_recs_ok8 : fam5.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam5_recs_ok9 : fam5.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam5_recs_ok10 : fam5.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam5_recs_ok11 : fam5.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam5_sub0_ok : fam5.subOK 0 = true := by decide +kernel

theorem fam5_sub1_ok : fam5.subOK 1 = true := by decide +kernel

theorem fam5_sub2_ok : fam5.subOK 2 = true := by decide +kernel

theorem fam5_sub3_ok : fam5.subOK 3 = true := by decide +kernel

theorem fam5_sub4_ok : fam5.subOK 4 = true := by decide +kernel

theorem fam5_sub5_ok : fam5.subOK 5 = true := by decide +kernel

theorem fam5_sub6_ok : fam5.subOK 6 = true := by decide +kernel

theorem fam5_sub7_ok : fam5.subOK 7 = true := by decide +kernel

theorem fam5_sub8_ok : fam5.subOK 8 = true := by decide +kernel

theorem fam5_sub9_ok : fam5.subOK 9 = true := by decide +kernel

theorem fam5_sub10_ok : fam5.subOK 10 = true := by decide +kernel

theorem fam5_sub11_ok : fam5.subOK 11 = true := by decide +kernel

theorem fam5_sub12_ok : fam5.subOK 12 = true := by decide +kernel

theorem fam5_sub13_ok : fam5.subOK 13 = true := by decide +kernel

theorem fam5_sub14_ok : fam5.subOK 14 = true := by decide +kernel

theorem fam5_sub15_ok : fam5.subOK 15 = true := by decide +kernel

theorem fam5_sub16_ok : fam5.subOK 16 = true := by decide +kernel

theorem fam5_sub17_ok : fam5.subOK 17 = true := by decide +kernel

theorem fam5_sub18_ok : fam5.subOK 18 = true := by decide +kernel

theorem fam5_sub19_ok : fam5.subOK 19 = true := by decide +kernel

theorem fam5_sub20_ok : fam5.subOK 20 = true := by decide +kernel

theorem fam5_recs : ∀ r ∈ fam5.recs, fam5.recOK r = true :=
  fam5.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [fam5_recs_ok0, fam5_recs_ok1, fam5_recs_ok2, fam5_recs_ok3, fam5_recs_ok4, fam5_recs_ok5, fam5_recs_ok6, fam5_recs_ok7, fam5_recs_ok8, fam5_recs_ok9, fam5_recs_ok10, fam5_recs_ok11])
    (by decide +kernel)

theorem fam5_subs : ∀ k < fam5.subs.length, fam5.subOK k = true := by
  intro k hk
  have h : fam5.subs.length = 21 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam5_sub0_ok, fam5_sub1_ok, fam5_sub2_ok, fam5_sub3_ok, fam5_sub4_ok, fam5_sub5_ok, fam5_sub6_ok, fam5_sub7_ok, fam5_sub8_ok, fam5_sub9_ok, fam5_sub10_ok, fam5_sub11_ok, fam5_sub12_ok, fam5_sub13_ok, fam5_sub14_ok, fam5_sub15_ok, fam5_sub16_ok, fam5_sub17_ok, fam5_sub18_ok, fam5_sub19_ok, fam5_sub20_ok]

end Kalai5.A16
