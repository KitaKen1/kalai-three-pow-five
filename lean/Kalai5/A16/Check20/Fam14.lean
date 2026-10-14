import Kalai5.A16.Data20.Fam14
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 14 at twenty facets. -/

namespace Kalai5.A16

theorem famT14_check : famT14.check21 = true := by decide +kernel

theorem famT14_recs_ok0 : famT14.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT14_recs_ok1 : famT14.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT14_recs_ok2 : famT14.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT14_recs_ok3 : famT14.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT14_recs_ok4 : famT14.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT14_recs_ok5 : famT14.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT14_recs_ok6 : famT14.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT14_recs_ok7 : famT14.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT14_recs_ok8 : famT14.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT14_recs_ok9 : famT14.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT14_recs_ok10 : famT14.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT14_recs_ok11 : famT14.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT14_recs_ok12 : famT14.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT14_recs_ok13 : famT14.recsOK (40 * 13) 40 = true := by decide +kernel

theorem famT14_sub0_ok : famT14.subOK 0 = true := by decide +kernel

theorem famT14_sub1_ok : famT14.subOK 1 = true := by decide +kernel

theorem famT14_sub2_ok : famT14.subOK 2 = true := by decide +kernel

theorem famT14_sub3_ok : famT14.subOK 3 = true := by decide +kernel

theorem famT14_sub4_ok : famT14.subOK 4 = true := by decide +kernel

theorem famT14_sub5_ok : famT14.subOK 5 = true := by decide +kernel

theorem famT14_sub6_ok : famT14.subOK 6 = true := by decide +kernel

theorem famT14_sub7_ok : famT14.subOK 7 = true := by decide +kernel

theorem famT14_sub8_ok : famT14.subOK 8 = true := by decide +kernel

theorem famT14_sub9_ok : famT14.subOK 9 = true := by decide +kernel

theorem famT14_sub10_ok : famT14.subOK 10 = true := by decide +kernel

theorem famT14_sub11_ok : famT14.subOK 11 = true := by decide +kernel

theorem famT14_sub12_ok : famT14.subOK 12 = true := by decide +kernel

theorem famT14_sub13_ok : famT14.subOK 13 = true := by decide +kernel

theorem famT14_sub14_ok : famT14.subOK 14 = true := by decide +kernel

theorem famT14_sub15_ok : famT14.subOK 15 = true := by decide +kernel

theorem famT14_sub16_ok : famT14.subOK 16 = true := by decide +kernel

theorem famT14_sub17_ok : famT14.subOK 17 = true := by decide +kernel

theorem famT14_sub18_ok : famT14.subOK 18 = true := by decide +kernel

theorem famT14_sub19_ok : famT14.subOK 19 = true := by decide +kernel

theorem famT14_sub20_ok : famT14.subOK 20 = true := by decide +kernel

theorem famT14_sub21_ok : famT14.subOK 21 = true := by decide +kernel

theorem famT14_sub22_ok : famT14.subOK 22 = true := by decide +kernel

theorem famT14_sub23_ok : famT14.subOK 23 = true := by decide +kernel

theorem famT14_sub24_ok : famT14.subOK 24 = true := by decide +kernel

theorem famT14_sub25_ok : famT14.subOK 25 = true := by decide +kernel

theorem famT14_sub26_ok : famT14.subOK 26 = true := by decide +kernel

theorem famT14_sub27_ok : famT14.subOK 27 = true := by decide +kernel

theorem famT14_sub28_ok : famT14.subOK 28 = true := by decide +kernel

theorem famT14_sub29_ok : famT14.subOK 29 = true := by decide +kernel

theorem famT14_sub30_ok : famT14.subOK 30 = true := by decide +kernel

theorem famT14_sub31_ok : famT14.subOK 31 = true := by decide +kernel

theorem famT14_sub32_ok : famT14.subOK 32 = true := by decide +kernel

theorem famT14_sub33_ok : famT14.subOK 33 = true := by decide +kernel

theorem famT14_sub34_ok : famT14.subOK 34 = true := by decide +kernel

theorem famT14_sub35_ok : famT14.subOK 35 = true := by decide +kernel

theorem famT14_sub36_ok : famT14.subOK 36 = true := by decide +kernel

theorem famT14_sub37_ok : famT14.subOK 37 = true := by decide +kernel

theorem famT14_sub38_ok : famT14.subOK 38 = true := by decide +kernel

theorem famT14_sub39_ok : famT14.subOK 39 = true := by decide +kernel

theorem famT14_sub40_ok : famT14.subOK 40 = true := by decide +kernel

theorem famT14_sub41_ok : famT14.subOK 41 = true := by decide +kernel

theorem famT14_sub42_ok : famT14.subOK 42 = true := by decide +kernel

theorem famT14_sub43_ok : famT14.subOK 43 = true := by decide +kernel

theorem famT14_sub44_ok : famT14.subOK 44 = true := by decide +kernel

theorem famT14_sub45_ok : famT14.subOK 45 = true := by decide +kernel

theorem famT14_recs : ∀ r ∈ famT14.recs, famT14.recOK r = true :=
  famT14.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [famT14_recs_ok0, famT14_recs_ok1, famT14_recs_ok2, famT14_recs_ok3, famT14_recs_ok4, famT14_recs_ok5, famT14_recs_ok6, famT14_recs_ok7, famT14_recs_ok8, famT14_recs_ok9, famT14_recs_ok10, famT14_recs_ok11, famT14_recs_ok12, famT14_recs_ok13])
    (by decide +kernel)

theorem famT14_subs : ∀ k < famT14.subs.length, famT14.subOK k = true := by
  intro k hk
  have h : famT14.subs.length = 46 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT14_sub0_ok, famT14_sub1_ok, famT14_sub2_ok, famT14_sub3_ok, famT14_sub4_ok, famT14_sub5_ok, famT14_sub6_ok, famT14_sub7_ok, famT14_sub8_ok, famT14_sub9_ok, famT14_sub10_ok, famT14_sub11_ok, famT14_sub12_ok, famT14_sub13_ok, famT14_sub14_ok, famT14_sub15_ok, famT14_sub16_ok, famT14_sub17_ok, famT14_sub18_ok, famT14_sub19_ok, famT14_sub20_ok, famT14_sub21_ok, famT14_sub22_ok, famT14_sub23_ok, famT14_sub24_ok, famT14_sub25_ok, famT14_sub26_ok, famT14_sub27_ok, famT14_sub28_ok, famT14_sub29_ok, famT14_sub30_ok, famT14_sub31_ok, famT14_sub32_ok, famT14_sub33_ok, famT14_sub34_ok, famT14_sub35_ok, famT14_sub36_ok, famT14_sub37_ok, famT14_sub38_ok, famT14_sub39_ok, famT14_sub40_ok, famT14_sub41_ok, famT14_sub42_ok, famT14_sub43_ok, famT14_sub44_ok, famT14_sub45_ok]

end Kalai5.A16
