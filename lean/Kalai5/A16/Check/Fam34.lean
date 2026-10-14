import Kalai5.A16.Data.Fam34
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 34. -/

namespace Kalai5.A16

theorem fam34_check : fam34.check = true := by decide +kernel

theorem fam34_recs_ok0 : fam34.recsOK (40 * 0) 40 = true := by decide +kernel

theorem fam34_recs_ok1 : fam34.recsOK (40 * 1) 40 = true := by decide +kernel

theorem fam34_recs_ok2 : fam34.recsOK (40 * 2) 40 = true := by decide +kernel

theorem fam34_recs_ok3 : fam34.recsOK (40 * 3) 40 = true := by decide +kernel

theorem fam34_recs_ok4 : fam34.recsOK (40 * 4) 40 = true := by decide +kernel

theorem fam34_recs_ok5 : fam34.recsOK (40 * 5) 40 = true := by decide +kernel

theorem fam34_recs_ok6 : fam34.recsOK (40 * 6) 40 = true := by decide +kernel

theorem fam34_recs_ok7 : fam34.recsOK (40 * 7) 40 = true := by decide +kernel

theorem fam34_recs_ok8 : fam34.recsOK (40 * 8) 40 = true := by decide +kernel

theorem fam34_recs_ok9 : fam34.recsOK (40 * 9) 40 = true := by decide +kernel

theorem fam34_recs_ok10 : fam34.recsOK (40 * 10) 40 = true := by decide +kernel

theorem fam34_recs_ok11 : fam34.recsOK (40 * 11) 40 = true := by decide +kernel

theorem fam34_recs_ok12 : fam34.recsOK (40 * 12) 40 = true := by decide +kernel

theorem fam34_sub0_ok : fam34.subOK 0 = true := by decide +kernel

theorem fam34_sub1_ok : fam34.subOK 1 = true := by decide +kernel

theorem fam34_sub2_ok : fam34.subOK 2 = true := by decide +kernel

theorem fam34_sub3_ok : fam34.subOK 3 = true := by decide +kernel

theorem fam34_sub4_ok : fam34.subOK 4 = true := by decide +kernel

theorem fam34_sub5_ok : fam34.subOK 5 = true := by decide +kernel

theorem fam34_sub6_ok : fam34.subOK 6 = true := by decide +kernel

theorem fam34_sub7_ok : fam34.subOK 7 = true := by decide +kernel

theorem fam34_sub8_ok : fam34.subOK 8 = true := by decide +kernel

theorem fam34_sub9_ok : fam34.subOK 9 = true := by decide +kernel

theorem fam34_sub10_ok : fam34.subOK 10 = true := by decide +kernel

theorem fam34_sub11_ok : fam34.subOK 11 = true := by decide +kernel

theorem fam34_sub12_ok : fam34.subOK 12 = true := by decide +kernel

theorem fam34_sub13_ok : fam34.subOK 13 = true := by decide +kernel

theorem fam34_sub14_ok : fam34.subOK 14 = true := by decide +kernel

theorem fam34_sub15_ok : fam34.subOK 15 = true := by decide +kernel

theorem fam34_sub16_ok : fam34.subOK 16 = true := by decide +kernel

theorem fam34_sub17_ok : fam34.subOK 17 = true := by decide +kernel

theorem fam34_sub18_ok : fam34.subOK 18 = true := by decide +kernel

theorem fam34_sub19_ok : fam34.subOK 19 = true := by decide +kernel

theorem fam34_sub20_ok : fam34.subOK 20 = true := by decide +kernel

theorem fam34_sub21_ok : fam34.subOK 21 = true := by decide +kernel

theorem fam34_sub22_ok : fam34.subOK 22 = true := by decide +kernel

theorem fam34_sub23_ok : fam34.subOK 23 = true := by decide +kernel

theorem fam34_sub24_ok : fam34.subOK 24 = true := by decide +kernel

theorem fam34_sub25_ok : fam34.subOK 25 = true := by decide +kernel

theorem fam34_sub26_ok : fam34.subOK 26 = true := by decide +kernel

theorem fam34_sub27_ok : fam34.subOK 27 = true := by decide +kernel

theorem fam34_sub28_ok : fam34.subOK 28 = true := by decide +kernel

theorem fam34_sub29_ok : fam34.subOK 29 = true := by decide +kernel

theorem fam34_sub30_ok : fam34.subOK 30 = true := by decide +kernel

theorem fam34_sub31_ok : fam34.subOK 31 = true := by decide +kernel

theorem fam34_sub32_ok : fam34.subOK 32 = true := by decide +kernel

theorem fam34_sub33_ok : fam34.subOK 33 = true := by decide +kernel

theorem fam34_sub34_ok : fam34.subOK 34 = true := by decide +kernel

theorem fam34_sub35_ok : fam34.subOK 35 = true := by decide +kernel

theorem fam34_sub36_ok : fam34.subOK 36 = true := by decide +kernel

theorem fam34_recs : ∀ r ∈ fam34.recs, fam34.recOK r = true :=
  fam34.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [fam34_recs_ok0, fam34_recs_ok1, fam34_recs_ok2, fam34_recs_ok3, fam34_recs_ok4, fam34_recs_ok5, fam34_recs_ok6, fam34_recs_ok7, fam34_recs_ok8, fam34_recs_ok9, fam34_recs_ok10, fam34_recs_ok11, fam34_recs_ok12])
    (by decide +kernel)

theorem fam34_subs : ∀ k < fam34.subs.length, fam34.subOK k = true := by
  intro k hk
  have h : fam34.subs.length = 37 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [fam34_sub0_ok, fam34_sub1_ok, fam34_sub2_ok, fam34_sub3_ok, fam34_sub4_ok, fam34_sub5_ok, fam34_sub6_ok, fam34_sub7_ok, fam34_sub8_ok, fam34_sub9_ok, fam34_sub10_ok, fam34_sub11_ok, fam34_sub12_ok, fam34_sub13_ok, fam34_sub14_ok, fam34_sub15_ok, fam34_sub16_ok, fam34_sub17_ok, fam34_sub18_ok, fam34_sub19_ok, fam34_sub20_ok, fam34_sub21_ok, fam34_sub22_ok, fam34_sub23_ok, fam34_sub24_ok, fam34_sub25_ok, fam34_sub26_ok, fam34_sub27_ok, fam34_sub28_ok, fam34_sub29_ok, fam34_sub30_ok, fam34_sub31_ok, fam34_sub32_ok, fam34_sub33_ok, fam34_sub34_ok, fam34_sub35_ok, fam34_sub36_ok]

end Kalai5.A16
