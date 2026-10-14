import Kalai5.A16.Data20.Fam25
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 25 at twenty facets. -/

namespace Kalai5.A16

theorem famT25_check : famT25.check21 = true := by decide +kernel

theorem famT25_recs_ok0 : famT25.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT25_recs_ok1 : famT25.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT25_recs_ok2 : famT25.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT25_recs_ok3 : famT25.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT25_recs_ok4 : famT25.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT25_recs_ok5 : famT25.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT25_recs_ok6 : famT25.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT25_recs_ok7 : famT25.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT25_recs_ok8 : famT25.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT25_recs_ok9 : famT25.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT25_recs_ok10 : famT25.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT25_recs_ok11 : famT25.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT25_recs_ok12 : famT25.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT25_recs_ok13 : famT25.recsOK (40 * 13) 40 = true := by decide +kernel

theorem famT25_sub0_ok : famT25.subOK 0 = true := by decide +kernel

theorem famT25_sub1_ok : famT25.subOK 1 = true := by decide +kernel

theorem famT25_sub2_ok : famT25.subOK 2 = true := by decide +kernel

theorem famT25_sub3_ok : famT25.subOK 3 = true := by decide +kernel

theorem famT25_sub4_ok : famT25.subOK 4 = true := by decide +kernel

theorem famT25_sub5_ok : famT25.subOK 5 = true := by decide +kernel

theorem famT25_sub6_ok : famT25.subOK 6 = true := by decide +kernel

theorem famT25_sub7_ok : famT25.subOK 7 = true := by decide +kernel

theorem famT25_sub8_ok : famT25.subOK 8 = true := by decide +kernel

theorem famT25_sub9_ok : famT25.subOK 9 = true := by decide +kernel

theorem famT25_sub10_ok : famT25.subOK 10 = true := by decide +kernel

theorem famT25_sub11_ok : famT25.subOK 11 = true := by decide +kernel

theorem famT25_sub12_ok : famT25.subOK 12 = true := by decide +kernel

theorem famT25_sub13_ok : famT25.subOK 13 = true := by decide +kernel

theorem famT25_sub14_ok : famT25.subOK 14 = true := by decide +kernel

theorem famT25_sub15_ok : famT25.subOK 15 = true := by decide +kernel

theorem famT25_sub16_ok : famT25.subOK 16 = true := by decide +kernel

theorem famT25_sub17_ok : famT25.subOK 17 = true := by decide +kernel

theorem famT25_sub18_ok : famT25.subOK 18 = true := by decide +kernel

theorem famT25_sub19_ok : famT25.subOK 19 = true := by decide +kernel

theorem famT25_sub20_ok : famT25.subOK 20 = true := by decide +kernel

theorem famT25_sub21_ok : famT25.subOK 21 = true := by decide +kernel

theorem famT25_sub22_ok : famT25.subOK 22 = true := by decide +kernel

theorem famT25_sub23_ok : famT25.subOK 23 = true := by decide +kernel

theorem famT25_sub24_ok : famT25.subOK 24 = true := by decide +kernel

theorem famT25_sub25_ok : famT25.subOK 25 = true := by decide +kernel

theorem famT25_sub26_ok : famT25.subOK 26 = true := by decide +kernel

theorem famT25_sub27_ok : famT25.subOK 27 = true := by decide +kernel

theorem famT25_sub28_ok : famT25.subOK 28 = true := by decide +kernel

theorem famT25_sub29_ok : famT25.subOK 29 = true := by decide +kernel

theorem famT25_sub30_ok : famT25.subOK 30 = true := by decide +kernel

theorem famT25_sub31_ok : famT25.subOK 31 = true := by decide +kernel

theorem famT25_sub32_ok : famT25.subOK 32 = true := by decide +kernel

theorem famT25_sub33_ok : famT25.subOK 33 = true := by decide +kernel

theorem famT25_sub34_ok : famT25.subOK 34 = true := by decide +kernel

theorem famT25_sub35_ok : famT25.subOK 35 = true := by decide +kernel

theorem famT25_sub36_ok : famT25.subOK 36 = true := by decide +kernel

theorem famT25_sub37_ok : famT25.subOK 37 = true := by decide +kernel

theorem famT25_sub38_ok : famT25.subOK 38 = true := by decide +kernel

theorem famT25_sub39_ok : famT25.subOK 39 = true := by decide +kernel

theorem famT25_sub40_ok : famT25.subOK 40 = true := by decide +kernel

theorem famT25_sub41_ok : famT25.subOK 41 = true := by decide +kernel

theorem famT25_sub42_ok : famT25.subOK 42 = true := by decide +kernel

theorem famT25_sub43_ok : famT25.subOK 43 = true := by decide +kernel

theorem famT25_sub44_ok : famT25.subOK 44 = true := by decide +kernel

theorem famT25_sub45_ok : famT25.subOK 45 = true := by decide +kernel

theorem famT25_recs : ∀ r ∈ famT25.recs, famT25.recOK r = true :=
  famT25.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [famT25_recs_ok0, famT25_recs_ok1, famT25_recs_ok2, famT25_recs_ok3, famT25_recs_ok4, famT25_recs_ok5, famT25_recs_ok6, famT25_recs_ok7, famT25_recs_ok8, famT25_recs_ok9, famT25_recs_ok10, famT25_recs_ok11, famT25_recs_ok12, famT25_recs_ok13])
    (by decide +kernel)

theorem famT25_subs : ∀ k < famT25.subs.length, famT25.subOK k = true := by
  intro k hk
  have h : famT25.subs.length = 46 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT25_sub0_ok, famT25_sub1_ok, famT25_sub2_ok, famT25_sub3_ok, famT25_sub4_ok, famT25_sub5_ok, famT25_sub6_ok, famT25_sub7_ok, famT25_sub8_ok, famT25_sub9_ok, famT25_sub10_ok, famT25_sub11_ok, famT25_sub12_ok, famT25_sub13_ok, famT25_sub14_ok, famT25_sub15_ok, famT25_sub16_ok, famT25_sub17_ok, famT25_sub18_ok, famT25_sub19_ok, famT25_sub20_ok, famT25_sub21_ok, famT25_sub22_ok, famT25_sub23_ok, famT25_sub24_ok, famT25_sub25_ok, famT25_sub26_ok, famT25_sub27_ok, famT25_sub28_ok, famT25_sub29_ok, famT25_sub30_ok, famT25_sub31_ok, famT25_sub32_ok, famT25_sub33_ok, famT25_sub34_ok, famT25_sub35_ok, famT25_sub36_ok, famT25_sub37_ok, famT25_sub38_ok, famT25_sub39_ok, famT25_sub40_ok, famT25_sub41_ok, famT25_sub42_ok, famT25_sub43_ok, famT25_sub44_ok, famT25_sub45_ok]

end Kalai5.A16
