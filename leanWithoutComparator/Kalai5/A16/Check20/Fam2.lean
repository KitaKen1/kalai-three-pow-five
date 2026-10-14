import Kalai5.A16.Data20.Fam2
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 2 at twenty facets. -/

namespace Kalai5.A16

theorem famT2_check : famT2.check21 = true := by decide +kernel

theorem famT2_recs_ok0 : famT2.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT2_recs_ok1 : famT2.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT2_recs_ok2 : famT2.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT2_recs_ok3 : famT2.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT2_recs_ok4 : famT2.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT2_recs_ok5 : famT2.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT2_recs_ok6 : famT2.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT2_recs_ok7 : famT2.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT2_recs_ok8 : famT2.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT2_recs_ok9 : famT2.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT2_sub0_ok : famT2.subOK 0 = true := by decide +kernel

theorem famT2_sub1_ok : famT2.subOK 1 = true := by decide +kernel

theorem famT2_sub2_ok : famT2.subOK 2 = true := by decide +kernel

theorem famT2_sub3_ok : famT2.subOK 3 = true := by decide +kernel

theorem famT2_sub4_ok : famT2.subOK 4 = true := by decide +kernel

theorem famT2_sub5_ok : famT2.subOK 5 = true := by decide +kernel

theorem famT2_sub6_ok : famT2.subOK 6 = true := by decide +kernel

theorem famT2_sub7_ok : famT2.subOK 7 = true := by decide +kernel

theorem famT2_sub8_ok : famT2.subOK 8 = true := by decide +kernel

theorem famT2_sub9_ok : famT2.subOK 9 = true := by decide +kernel

theorem famT2_sub10_ok : famT2.subOK 10 = true := by decide +kernel

theorem famT2_sub11_ok : famT2.subOK 11 = true := by decide +kernel

theorem famT2_sub12_ok : famT2.subOK 12 = true := by decide +kernel

theorem famT2_sub13_ok : famT2.subOK 13 = true := by decide +kernel

theorem famT2_sub14_ok : famT2.subOK 14 = true := by decide +kernel

theorem famT2_sub15_ok : famT2.subOK 15 = true := by decide +kernel

theorem famT2_sub16_ok : famT2.subOK 16 = true := by decide +kernel

theorem famT2_sub17_ok : famT2.subOK 17 = true := by decide +kernel

theorem famT2_sub18_ok : famT2.subOK 18 = true := by decide +kernel

theorem famT2_sub19_ok : famT2.subOK 19 = true := by decide +kernel

theorem famT2_sub20_ok : famT2.subOK 20 = true := by decide +kernel

theorem famT2_sub21_ok : famT2.subOK 21 = true := by decide +kernel

theorem famT2_sub22_ok : famT2.subOK 22 = true := by decide +kernel

theorem famT2_sub23_ok : famT2.subOK 23 = true := by decide +kernel

theorem famT2_sub24_ok : famT2.subOK 24 = true := by decide +kernel

theorem famT2_sub25_ok : famT2.subOK 25 = true := by decide +kernel

theorem famT2_sub26_ok : famT2.subOK 26 = true := by decide +kernel

theorem famT2_sub27_ok : famT2.subOK 27 = true := by decide +kernel

theorem famT2_sub28_ok : famT2.subOK 28 = true := by decide +kernel

theorem famT2_sub29_ok : famT2.subOK 29 = true := by decide +kernel

theorem famT2_sub30_ok : famT2.subOK 30 = true := by decide +kernel

theorem famT2_sub31_ok : famT2.subOK 31 = true := by decide +kernel

theorem famT2_sub32_ok : famT2.subOK 32 = true := by decide +kernel

theorem famT2_sub33_ok : famT2.subOK 33 = true := by decide +kernel

theorem famT2_sub34_ok : famT2.subOK 34 = true := by decide +kernel

theorem famT2_sub35_ok : famT2.subOK 35 = true := by decide +kernel

theorem famT2_sub36_ok : famT2.subOK 36 = true := by decide +kernel

theorem famT2_sub37_ok : famT2.subOK 37 = true := by decide +kernel

theorem famT2_sub38_ok : famT2.subOK 38 = true := by decide +kernel

theorem famT2_sub39_ok : famT2.subOK 39 = true := by decide +kernel

theorem famT2_sub40_ok : famT2.subOK 40 = true := by decide +kernel

theorem famT2_sub41_ok : famT2.subOK 41 = true := by decide +kernel

theorem famT2_sub42_ok : famT2.subOK 42 = true := by decide +kernel

theorem famT2_sub43_ok : famT2.subOK 43 = true := by decide +kernel

theorem famT2_sub44_ok : famT2.subOK 44 = true := by decide +kernel

theorem famT2_sub45_ok : famT2.subOK 45 = true := by decide +kernel

theorem famT2_recs : ∀ r ∈ famT2.recs, famT2.recOK r = true :=
  famT2.recs_of_chunks 10 (fun c hc => by
    interval_cases c
    exacts [famT2_recs_ok0, famT2_recs_ok1, famT2_recs_ok2, famT2_recs_ok3, famT2_recs_ok4, famT2_recs_ok5, famT2_recs_ok6, famT2_recs_ok7, famT2_recs_ok8, famT2_recs_ok9])
    (by decide +kernel)

theorem famT2_subs : ∀ k < famT2.subs.length, famT2.subOK k = true := by
  intro k hk
  have h : famT2.subs.length = 46 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT2_sub0_ok, famT2_sub1_ok, famT2_sub2_ok, famT2_sub3_ok, famT2_sub4_ok, famT2_sub5_ok, famT2_sub6_ok, famT2_sub7_ok, famT2_sub8_ok, famT2_sub9_ok, famT2_sub10_ok, famT2_sub11_ok, famT2_sub12_ok, famT2_sub13_ok, famT2_sub14_ok, famT2_sub15_ok, famT2_sub16_ok, famT2_sub17_ok, famT2_sub18_ok, famT2_sub19_ok, famT2_sub20_ok, famT2_sub21_ok, famT2_sub22_ok, famT2_sub23_ok, famT2_sub24_ok, famT2_sub25_ok, famT2_sub26_ok, famT2_sub27_ok, famT2_sub28_ok, famT2_sub29_ok, famT2_sub30_ok, famT2_sub31_ok, famT2_sub32_ok, famT2_sub33_ok, famT2_sub34_ok, famT2_sub35_ok, famT2_sub36_ok, famT2_sub37_ok, famT2_sub38_ok, famT2_sub39_ok, famT2_sub40_ok, famT2_sub41_ok, famT2_sub42_ok, famT2_sub43_ok, famT2_sub44_ok, famT2_sub45_ok]

end Kalai5.A16
