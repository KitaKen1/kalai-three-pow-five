import Kalai5.A16.Data20.Fam23
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 23 at twenty facets. -/

namespace Kalai5.A16

theorem famT23_check : famT23.check21 = true := by decide +kernel

theorem famT23_recs_ok0 : famT23.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT23_recs_ok1 : famT23.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT23_recs_ok2 : famT23.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT23_recs_ok3 : famT23.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT23_recs_ok4 : famT23.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT23_recs_ok5 : famT23.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT23_recs_ok6 : famT23.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT23_recs_ok7 : famT23.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT23_recs_ok8 : famT23.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT23_recs_ok9 : famT23.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT23_recs_ok10 : famT23.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT23_recs_ok11 : famT23.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT23_recs_ok12 : famT23.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT23_recs_ok13 : famT23.recsOK (40 * 13) 40 = true := by decide +kernel

theorem famT23_recs_ok14 : famT23.recsOK (40 * 14) 40 = true := by decide +kernel

theorem famT23_sub0_ok : famT23.subOK 0 = true := by decide +kernel

theorem famT23_sub1_ok : famT23.subOK 1 = true := by decide +kernel

theorem famT23_sub2_ok : famT23.subOK 2 = true := by decide +kernel

theorem famT23_sub3_ok : famT23.subOK 3 = true := by decide +kernel

theorem famT23_sub4_ok : famT23.subOK 4 = true := by decide +kernel

theorem famT23_sub5_ok : famT23.subOK 5 = true := by decide +kernel

theorem famT23_sub6_ok : famT23.subOK 6 = true := by decide +kernel

theorem famT23_sub7_ok : famT23.subOK 7 = true := by decide +kernel

theorem famT23_sub8_ok : famT23.subOK 8 = true := by decide +kernel

theorem famT23_sub9_ok : famT23.subOK 9 = true := by decide +kernel

theorem famT23_sub10_ok : famT23.subOK 10 = true := by decide +kernel

theorem famT23_sub11_ok : famT23.subOK 11 = true := by decide +kernel

theorem famT23_sub12_ok : famT23.subOK 12 = true := by decide +kernel

theorem famT23_sub13_ok : famT23.subOK 13 = true := by decide +kernel

theorem famT23_sub14_ok : famT23.subOK 14 = true := by decide +kernel

theorem famT23_sub15_ok : famT23.subOK 15 = true := by decide +kernel

theorem famT23_sub16_ok : famT23.subOK 16 = true := by decide +kernel

theorem famT23_sub17_ok : famT23.subOK 17 = true := by decide +kernel

theorem famT23_sub18_ok : famT23.subOK 18 = true := by decide +kernel

theorem famT23_sub19_ok : famT23.subOK 19 = true := by decide +kernel

theorem famT23_sub20_ok : famT23.subOK 20 = true := by decide +kernel

theorem famT23_sub21_ok : famT23.subOK 21 = true := by decide +kernel

theorem famT23_sub22_ok : famT23.subOK 22 = true := by decide +kernel

theorem famT23_sub23_ok : famT23.subOK 23 = true := by decide +kernel

theorem famT23_sub24_ok : famT23.subOK 24 = true := by decide +kernel

theorem famT23_sub25_ok : famT23.subOK 25 = true := by decide +kernel

theorem famT23_sub26_ok : famT23.subOK 26 = true := by decide +kernel

theorem famT23_sub27_ok : famT23.subOK 27 = true := by decide +kernel

theorem famT23_sub28_ok : famT23.subOK 28 = true := by decide +kernel

theorem famT23_sub29_ok : famT23.subOK 29 = true := by decide +kernel

theorem famT23_sub30_ok : famT23.subOK 30 = true := by decide +kernel

theorem famT23_sub31_ok : famT23.subOK 31 = true := by decide +kernel

theorem famT23_sub32_ok : famT23.subOK 32 = true := by decide +kernel

theorem famT23_sub33_ok : famT23.subOK 33 = true := by decide +kernel

theorem famT23_sub34_ok : famT23.subOK 34 = true := by decide +kernel

theorem famT23_sub35_ok : famT23.subOK 35 = true := by decide +kernel

theorem famT23_sub36_ok : famT23.subOK 36 = true := by decide +kernel

theorem famT23_sub37_ok : famT23.subOK 37 = true := by decide +kernel

theorem famT23_sub38_ok : famT23.subOK 38 = true := by decide +kernel

theorem famT23_sub39_ok : famT23.subOK 39 = true := by decide +kernel

theorem famT23_sub40_ok : famT23.subOK 40 = true := by decide +kernel

theorem famT23_recs : ∀ r ∈ famT23.recs, famT23.recOK r = true :=
  famT23.recs_of_chunks 15 (fun c hc => by
    interval_cases c
    exacts [famT23_recs_ok0, famT23_recs_ok1, famT23_recs_ok2, famT23_recs_ok3, famT23_recs_ok4, famT23_recs_ok5, famT23_recs_ok6, famT23_recs_ok7, famT23_recs_ok8, famT23_recs_ok9, famT23_recs_ok10, famT23_recs_ok11, famT23_recs_ok12, famT23_recs_ok13, famT23_recs_ok14])
    (by decide +kernel)

theorem famT23_subs : ∀ k < famT23.subs.length, famT23.subOK k = true := by
  intro k hk
  have h : famT23.subs.length = 41 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT23_sub0_ok, famT23_sub1_ok, famT23_sub2_ok, famT23_sub3_ok, famT23_sub4_ok, famT23_sub5_ok, famT23_sub6_ok, famT23_sub7_ok, famT23_sub8_ok, famT23_sub9_ok, famT23_sub10_ok, famT23_sub11_ok, famT23_sub12_ok, famT23_sub13_ok, famT23_sub14_ok, famT23_sub15_ok, famT23_sub16_ok, famT23_sub17_ok, famT23_sub18_ok, famT23_sub19_ok, famT23_sub20_ok, famT23_sub21_ok, famT23_sub22_ok, famT23_sub23_ok, famT23_sub24_ok, famT23_sub25_ok, famT23_sub26_ok, famT23_sub27_ok, famT23_sub28_ok, famT23_sub29_ok, famT23_sub30_ok, famT23_sub31_ok, famT23_sub32_ok, famT23_sub33_ok, famT23_sub34_ok, famT23_sub35_ok, famT23_sub36_ok, famT23_sub37_ok, famT23_sub38_ok, famT23_sub39_ok, famT23_sub40_ok]

end Kalai5.A16
