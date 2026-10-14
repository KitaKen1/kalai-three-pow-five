import Kalai5.A16.Data20.Fam29
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 29 at twenty facets. -/

namespace Kalai5.A16

theorem famT29_check : famT29.check21 = true := by decide +kernel

theorem famT29_recs_ok0 : famT29.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT29_recs_ok1 : famT29.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT29_recs_ok2 : famT29.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT29_recs_ok3 : famT29.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT29_recs_ok4 : famT29.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT29_recs_ok5 : famT29.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT29_recs_ok6 : famT29.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT29_recs_ok7 : famT29.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT29_recs_ok8 : famT29.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT29_recs_ok9 : famT29.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT29_recs_ok10 : famT29.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT29_recs_ok11 : famT29.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT29_recs_ok12 : famT29.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT29_recs_ok13 : famT29.recsOK (40 * 13) 40 = true := by decide +kernel

theorem famT29_sub0_ok : famT29.subOK 0 = true := by decide +kernel

theorem famT29_sub1_ok : famT29.subOK 1 = true := by decide +kernel

theorem famT29_sub2_ok : famT29.subOK 2 = true := by decide +kernel

theorem famT29_sub3_ok : famT29.subOK 3 = true := by decide +kernel

theorem famT29_sub4_ok : famT29.subOK 4 = true := by decide +kernel

theorem famT29_sub5_ok : famT29.subOK 5 = true := by decide +kernel

theorem famT29_sub6_ok : famT29.subOK 6 = true := by decide +kernel

theorem famT29_sub7_ok : famT29.subOK 7 = true := by decide +kernel

theorem famT29_sub8_ok : famT29.subOK 8 = true := by decide +kernel

theorem famT29_sub9_ok : famT29.subOK 9 = true := by decide +kernel

theorem famT29_sub10_ok : famT29.subOK 10 = true := by decide +kernel

theorem famT29_sub11_ok : famT29.subOK 11 = true := by decide +kernel

theorem famT29_sub12_ok : famT29.subOK 12 = true := by decide +kernel

theorem famT29_sub13_ok : famT29.subOK 13 = true := by decide +kernel

theorem famT29_sub14_ok : famT29.subOK 14 = true := by decide +kernel

theorem famT29_sub15_ok : famT29.subOK 15 = true := by decide +kernel

theorem famT29_sub16_ok : famT29.subOK 16 = true := by decide +kernel

theorem famT29_sub17_ok : famT29.subOK 17 = true := by decide +kernel

theorem famT29_sub18_ok : famT29.subOK 18 = true := by decide +kernel

theorem famT29_sub19_ok : famT29.subOK 19 = true := by decide +kernel

theorem famT29_sub20_ok : famT29.subOK 20 = true := by decide +kernel

theorem famT29_sub21_ok : famT29.subOK 21 = true := by decide +kernel

theorem famT29_sub22_ok : famT29.subOK 22 = true := by decide +kernel

theorem famT29_sub23_ok : famT29.subOK 23 = true := by decide +kernel

theorem famT29_sub24_ok : famT29.subOK 24 = true := by decide +kernel

theorem famT29_sub25_ok : famT29.subOK 25 = true := by decide +kernel

theorem famT29_sub26_ok : famT29.subOK 26 = true := by decide +kernel

theorem famT29_sub27_ok : famT29.subOK 27 = true := by decide +kernel

theorem famT29_sub28_ok : famT29.subOK 28 = true := by decide +kernel

theorem famT29_sub29_ok : famT29.subOK 29 = true := by decide +kernel

theorem famT29_sub30_ok : famT29.subOK 30 = true := by decide +kernel

theorem famT29_sub31_ok : famT29.subOK 31 = true := by decide +kernel

theorem famT29_sub32_ok : famT29.subOK 32 = true := by decide +kernel

theorem famT29_sub33_ok : famT29.subOK 33 = true := by decide +kernel

theorem famT29_sub34_ok : famT29.subOK 34 = true := by decide +kernel

theorem famT29_sub35_ok : famT29.subOK 35 = true := by decide +kernel

theorem famT29_sub36_ok : famT29.subOK 36 = true := by decide +kernel

theorem famT29_sub37_ok : famT29.subOK 37 = true := by decide +kernel

theorem famT29_sub38_ok : famT29.subOK 38 = true := by decide +kernel

theorem famT29_sub39_ok : famT29.subOK 39 = true := by decide +kernel

theorem famT29_sub40_ok : famT29.subOK 40 = true := by decide +kernel

theorem famT29_sub41_ok : famT29.subOK 41 = true := by decide +kernel

theorem famT29_sub42_ok : famT29.subOK 42 = true := by decide +kernel

theorem famT29_sub43_ok : famT29.subOK 43 = true := by decide +kernel

theorem famT29_sub44_ok : famT29.subOK 44 = true := by decide +kernel

theorem famT29_recs : ∀ r ∈ famT29.recs, famT29.recOK r = true :=
  famT29.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [famT29_recs_ok0, famT29_recs_ok1, famT29_recs_ok2, famT29_recs_ok3, famT29_recs_ok4, famT29_recs_ok5, famT29_recs_ok6, famT29_recs_ok7, famT29_recs_ok8, famT29_recs_ok9, famT29_recs_ok10, famT29_recs_ok11, famT29_recs_ok12, famT29_recs_ok13])
    (by decide +kernel)

theorem famT29_subs : ∀ k < famT29.subs.length, famT29.subOK k = true := by
  intro k hk
  have h : famT29.subs.length = 45 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT29_sub0_ok, famT29_sub1_ok, famT29_sub2_ok, famT29_sub3_ok, famT29_sub4_ok, famT29_sub5_ok, famT29_sub6_ok, famT29_sub7_ok, famT29_sub8_ok, famT29_sub9_ok, famT29_sub10_ok, famT29_sub11_ok, famT29_sub12_ok, famT29_sub13_ok, famT29_sub14_ok, famT29_sub15_ok, famT29_sub16_ok, famT29_sub17_ok, famT29_sub18_ok, famT29_sub19_ok, famT29_sub20_ok, famT29_sub21_ok, famT29_sub22_ok, famT29_sub23_ok, famT29_sub24_ok, famT29_sub25_ok, famT29_sub26_ok, famT29_sub27_ok, famT29_sub28_ok, famT29_sub29_ok, famT29_sub30_ok, famT29_sub31_ok, famT29_sub32_ok, famT29_sub33_ok, famT29_sub34_ok, famT29_sub35_ok, famT29_sub36_ok, famT29_sub37_ok, famT29_sub38_ok, famT29_sub39_ok, famT29_sub40_ok, famT29_sub41_ok, famT29_sub42_ok, famT29_sub43_ok, famT29_sub44_ok]

end Kalai5.A16
