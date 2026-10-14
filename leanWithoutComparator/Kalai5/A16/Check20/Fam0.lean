import Kalai5.A16.Data20.Fam0
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 0 at twenty facets. -/

namespace Kalai5.A16

theorem famT0_check : famT0.check21 = true := by decide +kernel

theorem famT0_recs_ok0 : famT0.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT0_recs_ok1 : famT0.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT0_recs_ok2 : famT0.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT0_recs_ok3 : famT0.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT0_recs_ok4 : famT0.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT0_recs_ok5 : famT0.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT0_recs_ok6 : famT0.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT0_recs_ok7 : famT0.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT0_recs_ok8 : famT0.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT0_recs_ok9 : famT0.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT0_sub0_ok : famT0.subOK 0 = true := by decide +kernel

theorem famT0_sub1_ok : famT0.subOK 1 = true := by decide +kernel

theorem famT0_sub2_ok : famT0.subOK 2 = true := by decide +kernel

theorem famT0_sub3_ok : famT0.subOK 3 = true := by decide +kernel

theorem famT0_sub4_ok : famT0.subOK 4 = true := by decide +kernel

theorem famT0_sub5_ok : famT0.subOK 5 = true := by decide +kernel

theorem famT0_sub6_ok : famT0.subOK 6 = true := by decide +kernel

theorem famT0_sub7_ok : famT0.subOK 7 = true := by decide +kernel

theorem famT0_sub8_ok : famT0.subOK 8 = true := by decide +kernel

theorem famT0_sub9_ok : famT0.subOK 9 = true := by decide +kernel

theorem famT0_sub10_ok : famT0.subOK 10 = true := by decide +kernel

theorem famT0_sub11_ok : famT0.subOK 11 = true := by decide +kernel

theorem famT0_sub12_ok : famT0.subOK 12 = true := by decide +kernel

theorem famT0_sub13_ok : famT0.subOK 13 = true := by decide +kernel

theorem famT0_sub14_ok : famT0.subOK 14 = true := by decide +kernel

theorem famT0_sub15_ok : famT0.subOK 15 = true := by decide +kernel

theorem famT0_sub16_ok : famT0.subOK 16 = true := by decide +kernel

theorem famT0_sub17_ok : famT0.subOK 17 = true := by decide +kernel

theorem famT0_sub18_ok : famT0.subOK 18 = true := by decide +kernel

theorem famT0_sub19_ok : famT0.subOK 19 = true := by decide +kernel

theorem famT0_sub20_ok : famT0.subOK 20 = true := by decide +kernel

theorem famT0_sub21_ok : famT0.subOK 21 = true := by decide +kernel

theorem famT0_sub22_ok : famT0.subOK 22 = true := by decide +kernel

theorem famT0_sub23_ok : famT0.subOK 23 = true := by decide +kernel

theorem famT0_sub24_ok : famT0.subOK 24 = true := by decide +kernel

theorem famT0_sub25_ok : famT0.subOK 25 = true := by decide +kernel

theorem famT0_sub26_ok : famT0.subOK 26 = true := by decide +kernel

theorem famT0_sub27_ok : famT0.subOK 27 = true := by decide +kernel

theorem famT0_sub28_ok : famT0.subOK 28 = true := by decide +kernel

theorem famT0_sub29_ok : famT0.subOK 29 = true := by decide +kernel

theorem famT0_sub30_ok : famT0.subOK 30 = true := by decide +kernel

theorem famT0_sub31_ok : famT0.subOK 31 = true := by decide +kernel

theorem famT0_sub32_ok : famT0.subOK 32 = true := by decide +kernel

theorem famT0_sub33_ok : famT0.subOK 33 = true := by decide +kernel

theorem famT0_sub34_ok : famT0.subOK 34 = true := by decide +kernel

theorem famT0_sub35_ok : famT0.subOK 35 = true := by decide +kernel

theorem famT0_sub36_ok : famT0.subOK 36 = true := by decide +kernel

theorem famT0_sub37_ok : famT0.subOK 37 = true := by decide +kernel

theorem famT0_sub38_ok : famT0.subOK 38 = true := by decide +kernel

theorem famT0_sub39_ok : famT0.subOK 39 = true := by decide +kernel

theorem famT0_sub40_ok : famT0.subOK 40 = true := by decide +kernel

theorem famT0_sub41_ok : famT0.subOK 41 = true := by decide +kernel

theorem famT0_sub42_ok : famT0.subOK 42 = true := by decide +kernel

theorem famT0_sub43_ok : famT0.subOK 43 = true := by decide +kernel

theorem famT0_sub44_ok : famT0.subOK 44 = true := by decide +kernel

theorem famT0_sub45_ok : famT0.subOK 45 = true := by decide +kernel

theorem famT0_recs : ∀ r ∈ famT0.recs, famT0.recOK r = true :=
  famT0.recs_of_chunks 10 (fun c hc => by
    interval_cases c
    exacts [famT0_recs_ok0, famT0_recs_ok1, famT0_recs_ok2, famT0_recs_ok3, famT0_recs_ok4, famT0_recs_ok5, famT0_recs_ok6, famT0_recs_ok7, famT0_recs_ok8, famT0_recs_ok9])
    (by decide +kernel)

theorem famT0_subs : ∀ k < famT0.subs.length, famT0.subOK k = true := by
  intro k hk
  have h : famT0.subs.length = 46 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT0_sub0_ok, famT0_sub1_ok, famT0_sub2_ok, famT0_sub3_ok, famT0_sub4_ok, famT0_sub5_ok, famT0_sub6_ok, famT0_sub7_ok, famT0_sub8_ok, famT0_sub9_ok, famT0_sub10_ok, famT0_sub11_ok, famT0_sub12_ok, famT0_sub13_ok, famT0_sub14_ok, famT0_sub15_ok, famT0_sub16_ok, famT0_sub17_ok, famT0_sub18_ok, famT0_sub19_ok, famT0_sub20_ok, famT0_sub21_ok, famT0_sub22_ok, famT0_sub23_ok, famT0_sub24_ok, famT0_sub25_ok, famT0_sub26_ok, famT0_sub27_ok, famT0_sub28_ok, famT0_sub29_ok, famT0_sub30_ok, famT0_sub31_ok, famT0_sub32_ok, famT0_sub33_ok, famT0_sub34_ok, famT0_sub35_ok, famT0_sub36_ok, famT0_sub37_ok, famT0_sub38_ok, famT0_sub39_ok, famT0_sub40_ok, famT0_sub41_ok, famT0_sub42_ok, famT0_sub43_ok, famT0_sub44_ok, famT0_sub45_ok]

end Kalai5.A16
