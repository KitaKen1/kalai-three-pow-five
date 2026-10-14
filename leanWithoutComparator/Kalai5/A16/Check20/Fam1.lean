import Kalai5.A16.Data20.Fam1
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 1 at twenty facets. -/

namespace Kalai5.A16

theorem famT1_check : famT1.check21 = true := by decide +kernel

theorem famT1_recs_ok0 : famT1.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT1_recs_ok1 : famT1.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT1_recs_ok2 : famT1.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT1_recs_ok3 : famT1.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT1_recs_ok4 : famT1.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT1_recs_ok5 : famT1.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT1_recs_ok6 : famT1.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT1_recs_ok7 : famT1.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT1_recs_ok8 : famT1.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT1_sub0_ok : famT1.subOK 0 = true := by decide +kernel

theorem famT1_sub1_ok : famT1.subOK 1 = true := by decide +kernel

theorem famT1_sub2_ok : famT1.subOK 2 = true := by decide +kernel

theorem famT1_sub3_ok : famT1.subOK 3 = true := by decide +kernel

theorem famT1_sub4_ok : famT1.subOK 4 = true := by decide +kernel

theorem famT1_sub5_ok : famT1.subOK 5 = true := by decide +kernel

theorem famT1_sub6_ok : famT1.subOK 6 = true := by decide +kernel

theorem famT1_sub7_ok : famT1.subOK 7 = true := by decide +kernel

theorem famT1_sub8_ok : famT1.subOK 8 = true := by decide +kernel

theorem famT1_sub9_ok : famT1.subOK 9 = true := by decide +kernel

theorem famT1_sub10_ok : famT1.subOK 10 = true := by decide +kernel

theorem famT1_sub11_ok : famT1.subOK 11 = true := by decide +kernel

theorem famT1_sub12_ok : famT1.subOK 12 = true := by decide +kernel

theorem famT1_sub13_ok : famT1.subOK 13 = true := by decide +kernel

theorem famT1_sub14_ok : famT1.subOK 14 = true := by decide +kernel

theorem famT1_sub15_ok : famT1.subOK 15 = true := by decide +kernel

theorem famT1_sub16_ok : famT1.subOK 16 = true := by decide +kernel

theorem famT1_sub17_ok : famT1.subOK 17 = true := by decide +kernel

theorem famT1_sub18_ok : famT1.subOK 18 = true := by decide +kernel

theorem famT1_sub19_ok : famT1.subOK 19 = true := by decide +kernel

theorem famT1_sub20_ok : famT1.subOK 20 = true := by decide +kernel

theorem famT1_sub21_ok : famT1.subOK 21 = true := by decide +kernel

theorem famT1_sub22_ok : famT1.subOK 22 = true := by decide +kernel

theorem famT1_sub23_ok : famT1.subOK 23 = true := by decide +kernel

theorem famT1_sub24_ok : famT1.subOK 24 = true := by decide +kernel

theorem famT1_sub25_ok : famT1.subOK 25 = true := by decide +kernel

theorem famT1_sub26_ok : famT1.subOK 26 = true := by decide +kernel

theorem famT1_sub27_ok : famT1.subOK 27 = true := by decide +kernel

theorem famT1_sub28_ok : famT1.subOK 28 = true := by decide +kernel

theorem famT1_sub29_ok : famT1.subOK 29 = true := by decide +kernel

theorem famT1_sub30_ok : famT1.subOK 30 = true := by decide +kernel

theorem famT1_sub31_ok : famT1.subOK 31 = true := by decide +kernel

theorem famT1_sub32_ok : famT1.subOK 32 = true := by decide +kernel

theorem famT1_sub33_ok : famT1.subOK 33 = true := by decide +kernel

theorem famT1_sub34_ok : famT1.subOK 34 = true := by decide +kernel

theorem famT1_sub35_ok : famT1.subOK 35 = true := by decide +kernel

theorem famT1_sub36_ok : famT1.subOK 36 = true := by decide +kernel

theorem famT1_sub37_ok : famT1.subOK 37 = true := by decide +kernel

theorem famT1_sub38_ok : famT1.subOK 38 = true := by decide +kernel

theorem famT1_sub39_ok : famT1.subOK 39 = true := by decide +kernel

theorem famT1_sub40_ok : famT1.subOK 40 = true := by decide +kernel

theorem famT1_sub41_ok : famT1.subOK 41 = true := by decide +kernel

theorem famT1_sub42_ok : famT1.subOK 42 = true := by decide +kernel

theorem famT1_sub43_ok : famT1.subOK 43 = true := by decide +kernel

theorem famT1_sub44_ok : famT1.subOK 44 = true := by decide +kernel

theorem famT1_sub45_ok : famT1.subOK 45 = true := by decide +kernel

theorem famT1_recs : ∀ r ∈ famT1.recs, famT1.recOK r = true :=
  famT1.recs_of_chunks 9 (fun c hc => by
    interval_cases c
    exacts [famT1_recs_ok0, famT1_recs_ok1, famT1_recs_ok2, famT1_recs_ok3, famT1_recs_ok4, famT1_recs_ok5, famT1_recs_ok6, famT1_recs_ok7, famT1_recs_ok8])
    (by decide +kernel)

theorem famT1_subs : ∀ k < famT1.subs.length, famT1.subOK k = true := by
  intro k hk
  have h : famT1.subs.length = 46 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT1_sub0_ok, famT1_sub1_ok, famT1_sub2_ok, famT1_sub3_ok, famT1_sub4_ok, famT1_sub5_ok, famT1_sub6_ok, famT1_sub7_ok, famT1_sub8_ok, famT1_sub9_ok, famT1_sub10_ok, famT1_sub11_ok, famT1_sub12_ok, famT1_sub13_ok, famT1_sub14_ok, famT1_sub15_ok, famT1_sub16_ok, famT1_sub17_ok, famT1_sub18_ok, famT1_sub19_ok, famT1_sub20_ok, famT1_sub21_ok, famT1_sub22_ok, famT1_sub23_ok, famT1_sub24_ok, famT1_sub25_ok, famT1_sub26_ok, famT1_sub27_ok, famT1_sub28_ok, famT1_sub29_ok, famT1_sub30_ok, famT1_sub31_ok, famT1_sub32_ok, famT1_sub33_ok, famT1_sub34_ok, famT1_sub35_ok, famT1_sub36_ok, famT1_sub37_ok, famT1_sub38_ok, famT1_sub39_ok, famT1_sub40_ok, famT1_sub41_ok, famT1_sub42_ok, famT1_sub43_ok, famT1_sub44_ok, famT1_sub45_ok]

end Kalai5.A16
