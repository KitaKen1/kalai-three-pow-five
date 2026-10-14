import Kalai5.A16.Data20.Fam30
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 30 at twenty facets. -/

namespace Kalai5.A16

theorem famT30_check : famT30.check21 = true := by decide +kernel

theorem famT30_recs_ok0 : famT30.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT30_recs_ok1 : famT30.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT30_recs_ok2 : famT30.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT30_recs_ok3 : famT30.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT30_recs_ok4 : famT30.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT30_recs_ok5 : famT30.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT30_recs_ok6 : famT30.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT30_recs_ok7 : famT30.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT30_recs_ok8 : famT30.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT30_recs_ok9 : famT30.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT30_recs_ok10 : famT30.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT30_recs_ok11 : famT30.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT30_recs_ok12 : famT30.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT30_recs_ok13 : famT30.recsOK (40 * 13) 40 = true := by decide +kernel

theorem famT30_sub0_ok : famT30.subOK 0 = true := by decide +kernel

theorem famT30_sub1_ok : famT30.subOK 1 = true := by decide +kernel

theorem famT30_sub2_ok : famT30.subOK 2 = true := by decide +kernel

theorem famT30_sub3_ok : famT30.subOK 3 = true := by decide +kernel

theorem famT30_sub4_ok : famT30.subOK 4 = true := by decide +kernel

theorem famT30_sub5_ok : famT30.subOK 5 = true := by decide +kernel

theorem famT30_sub6_ok : famT30.subOK 6 = true := by decide +kernel

theorem famT30_sub7_ok : famT30.subOK 7 = true := by decide +kernel

theorem famT30_sub8_ok : famT30.subOK 8 = true := by decide +kernel

theorem famT30_sub9_ok : famT30.subOK 9 = true := by decide +kernel

theorem famT30_sub10_ok : famT30.subOK 10 = true := by decide +kernel

theorem famT30_sub11_ok : famT30.subOK 11 = true := by decide +kernel

theorem famT30_sub12_ok : famT30.subOK 12 = true := by decide +kernel

theorem famT30_sub13_ok : famT30.subOK 13 = true := by decide +kernel

theorem famT30_sub14_ok : famT30.subOK 14 = true := by decide +kernel

theorem famT30_sub15_ok : famT30.subOK 15 = true := by decide +kernel

theorem famT30_sub16_ok : famT30.subOK 16 = true := by decide +kernel

theorem famT30_sub17_ok : famT30.subOK 17 = true := by decide +kernel

theorem famT30_sub18_ok : famT30.subOK 18 = true := by decide +kernel

theorem famT30_sub19_ok : famT30.subOK 19 = true := by decide +kernel

theorem famT30_sub20_ok : famT30.subOK 20 = true := by decide +kernel

theorem famT30_sub21_ok : famT30.subOK 21 = true := by decide +kernel

theorem famT30_sub22_ok : famT30.subOK 22 = true := by decide +kernel

theorem famT30_sub23_ok : famT30.subOK 23 = true := by decide +kernel

theorem famT30_sub24_ok : famT30.subOK 24 = true := by decide +kernel

theorem famT30_sub25_ok : famT30.subOK 25 = true := by decide +kernel

theorem famT30_sub26_ok : famT30.subOK 26 = true := by decide +kernel

theorem famT30_sub27_ok : famT30.subOK 27 = true := by decide +kernel

theorem famT30_sub28_ok : famT30.subOK 28 = true := by decide +kernel

theorem famT30_sub29_ok : famT30.subOK 29 = true := by decide +kernel

theorem famT30_sub30_ok : famT30.subOK 30 = true := by decide +kernel

theorem famT30_sub31_ok : famT30.subOK 31 = true := by decide +kernel

theorem famT30_sub32_ok : famT30.subOK 32 = true := by decide +kernel

theorem famT30_sub33_ok : famT30.subOK 33 = true := by decide +kernel

theorem famT30_sub34_ok : famT30.subOK 34 = true := by decide +kernel

theorem famT30_sub35_ok : famT30.subOK 35 = true := by decide +kernel

theorem famT30_sub36_ok : famT30.subOK 36 = true := by decide +kernel

theorem famT30_sub37_ok : famT30.subOK 37 = true := by decide +kernel

theorem famT30_sub38_ok : famT30.subOK 38 = true := by decide +kernel

theorem famT30_sub39_ok : famT30.subOK 39 = true := by decide +kernel

theorem famT30_sub40_ok : famT30.subOK 40 = true := by decide +kernel

theorem famT30_recs : ∀ r ∈ famT30.recs, famT30.recOK r = true :=
  famT30.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [famT30_recs_ok0, famT30_recs_ok1, famT30_recs_ok2, famT30_recs_ok3, famT30_recs_ok4, famT30_recs_ok5, famT30_recs_ok6, famT30_recs_ok7, famT30_recs_ok8, famT30_recs_ok9, famT30_recs_ok10, famT30_recs_ok11, famT30_recs_ok12, famT30_recs_ok13])
    (by decide +kernel)

theorem famT30_subs : ∀ k < famT30.subs.length, famT30.subOK k = true := by
  intro k hk
  have h : famT30.subs.length = 41 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT30_sub0_ok, famT30_sub1_ok, famT30_sub2_ok, famT30_sub3_ok, famT30_sub4_ok, famT30_sub5_ok, famT30_sub6_ok, famT30_sub7_ok, famT30_sub8_ok, famT30_sub9_ok, famT30_sub10_ok, famT30_sub11_ok, famT30_sub12_ok, famT30_sub13_ok, famT30_sub14_ok, famT30_sub15_ok, famT30_sub16_ok, famT30_sub17_ok, famT30_sub18_ok, famT30_sub19_ok, famT30_sub20_ok, famT30_sub21_ok, famT30_sub22_ok, famT30_sub23_ok, famT30_sub24_ok, famT30_sub25_ok, famT30_sub26_ok, famT30_sub27_ok, famT30_sub28_ok, famT30_sub29_ok, famT30_sub30_ok, famT30_sub31_ok, famT30_sub32_ok, famT30_sub33_ok, famT30_sub34_ok, famT30_sub35_ok, famT30_sub36_ok, famT30_sub37_ok, famT30_sub38_ok, famT30_sub39_ok, famT30_sub40_ok]

end Kalai5.A16
