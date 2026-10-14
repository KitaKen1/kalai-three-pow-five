import Kalai5.A16.Data20.Fam35
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 35 at twenty facets. -/

namespace Kalai5.A16

theorem famT35_check : famT35.check21 = true := by decide +kernel

theorem famT35_recs_ok0 : famT35.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT35_recs_ok1 : famT35.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT35_recs_ok2 : famT35.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT35_recs_ok3 : famT35.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT35_recs_ok4 : famT35.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT35_recs_ok5 : famT35.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT35_recs_ok6 : famT35.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT35_recs_ok7 : famT35.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT35_recs_ok8 : famT35.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT35_recs_ok9 : famT35.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT35_recs_ok10 : famT35.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT35_recs_ok11 : famT35.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT35_recs_ok12 : famT35.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT35_recs_ok13 : famT35.recsOK (40 * 13) 40 = true := by decide +kernel

theorem famT35_sub0_ok : famT35.subOK 0 = true := by decide +kernel

theorem famT35_sub1_ok : famT35.subOK 1 = true := by decide +kernel

theorem famT35_sub2_ok : famT35.subOK 2 = true := by decide +kernel

theorem famT35_sub3_ok : famT35.subOK 3 = true := by decide +kernel

theorem famT35_sub4_ok : famT35.subOK 4 = true := by decide +kernel

theorem famT35_sub5_ok : famT35.subOK 5 = true := by decide +kernel

theorem famT35_sub6_ok : famT35.subOK 6 = true := by decide +kernel

theorem famT35_sub7_ok : famT35.subOK 7 = true := by decide +kernel

theorem famT35_sub8_ok : famT35.subOK 8 = true := by decide +kernel

theorem famT35_sub9_ok : famT35.subOK 9 = true := by decide +kernel

theorem famT35_sub10_ok : famT35.subOK 10 = true := by decide +kernel

theorem famT35_sub11_ok : famT35.subOK 11 = true := by decide +kernel

theorem famT35_sub12_ok : famT35.subOK 12 = true := by decide +kernel

theorem famT35_sub13_ok : famT35.subOK 13 = true := by decide +kernel

theorem famT35_sub14_ok : famT35.subOK 14 = true := by decide +kernel

theorem famT35_sub15_ok : famT35.subOK 15 = true := by decide +kernel

theorem famT35_sub16_ok : famT35.subOK 16 = true := by decide +kernel

theorem famT35_sub17_ok : famT35.subOK 17 = true := by decide +kernel

theorem famT35_sub18_ok : famT35.subOK 18 = true := by decide +kernel

theorem famT35_sub19_ok : famT35.subOK 19 = true := by decide +kernel

theorem famT35_sub20_ok : famT35.subOK 20 = true := by decide +kernel

theorem famT35_sub21_ok : famT35.subOK 21 = true := by decide +kernel

theorem famT35_sub22_ok : famT35.subOK 22 = true := by decide +kernel

theorem famT35_sub23_ok : famT35.subOK 23 = true := by decide +kernel

theorem famT35_sub24_ok : famT35.subOK 24 = true := by decide +kernel

theorem famT35_sub25_ok : famT35.subOK 25 = true := by decide +kernel

theorem famT35_sub26_ok : famT35.subOK 26 = true := by decide +kernel

theorem famT35_sub27_ok : famT35.subOK 27 = true := by decide +kernel

theorem famT35_sub28_ok : famT35.subOK 28 = true := by decide +kernel

theorem famT35_sub29_ok : famT35.subOK 29 = true := by decide +kernel

theorem famT35_sub30_ok : famT35.subOK 30 = true := by decide +kernel

theorem famT35_sub31_ok : famT35.subOK 31 = true := by decide +kernel

theorem famT35_sub32_ok : famT35.subOK 32 = true := by decide +kernel

theorem famT35_sub33_ok : famT35.subOK 33 = true := by decide +kernel

theorem famT35_sub34_ok : famT35.subOK 34 = true := by decide +kernel

theorem famT35_sub35_ok : famT35.subOK 35 = true := by decide +kernel

theorem famT35_sub36_ok : famT35.subOK 36 = true := by decide +kernel

theorem famT35_sub37_ok : famT35.subOK 37 = true := by decide +kernel

theorem famT35_sub38_ok : famT35.subOK 38 = true := by decide +kernel

theorem famT35_sub39_ok : famT35.subOK 39 = true := by decide +kernel

theorem famT35_sub40_ok : famT35.subOK 40 = true := by decide +kernel

theorem famT35_sub41_ok : famT35.subOK 41 = true := by decide +kernel

theorem famT35_sub42_ok : famT35.subOK 42 = true := by decide +kernel

theorem famT35_sub43_ok : famT35.subOK 43 = true := by decide +kernel

theorem famT35_sub44_ok : famT35.subOK 44 = true := by decide +kernel

theorem famT35_sub45_ok : famT35.subOK 45 = true := by decide +kernel

theorem famT35_sub46_ok : famT35.subOK 46 = true := by decide +kernel

theorem famT35_sub47_ok : famT35.subOK 47 = true := by decide +kernel

theorem famT35_sub48_ok : famT35.subOK 48 = true := by decide +kernel

theorem famT35_sub49_ok : famT35.subOK 49 = true := by decide +kernel

theorem famT35_recs : ∀ r ∈ famT35.recs, famT35.recOK r = true :=
  famT35.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [famT35_recs_ok0, famT35_recs_ok1, famT35_recs_ok2, famT35_recs_ok3, famT35_recs_ok4, famT35_recs_ok5, famT35_recs_ok6, famT35_recs_ok7, famT35_recs_ok8, famT35_recs_ok9, famT35_recs_ok10, famT35_recs_ok11, famT35_recs_ok12, famT35_recs_ok13])
    (by decide +kernel)

theorem famT35_subs : ∀ k < famT35.subs.length, famT35.subOK k = true := by
  intro k hk
  have h : famT35.subs.length = 50 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT35_sub0_ok, famT35_sub1_ok, famT35_sub2_ok, famT35_sub3_ok, famT35_sub4_ok, famT35_sub5_ok, famT35_sub6_ok, famT35_sub7_ok, famT35_sub8_ok, famT35_sub9_ok, famT35_sub10_ok, famT35_sub11_ok, famT35_sub12_ok, famT35_sub13_ok, famT35_sub14_ok, famT35_sub15_ok, famT35_sub16_ok, famT35_sub17_ok, famT35_sub18_ok, famT35_sub19_ok, famT35_sub20_ok, famT35_sub21_ok, famT35_sub22_ok, famT35_sub23_ok, famT35_sub24_ok, famT35_sub25_ok, famT35_sub26_ok, famT35_sub27_ok, famT35_sub28_ok, famT35_sub29_ok, famT35_sub30_ok, famT35_sub31_ok, famT35_sub32_ok, famT35_sub33_ok, famT35_sub34_ok, famT35_sub35_ok, famT35_sub36_ok, famT35_sub37_ok, famT35_sub38_ok, famT35_sub39_ok, famT35_sub40_ok, famT35_sub41_ok, famT35_sub42_ok, famT35_sub43_ok, famT35_sub44_ok, famT35_sub45_ok, famT35_sub46_ok, famT35_sub47_ok, famT35_sub48_ok, famT35_sub49_ok]

end Kalai5.A16
