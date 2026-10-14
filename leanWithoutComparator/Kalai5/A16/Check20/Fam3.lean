import Kalai5.A16.Data20.Fam3
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 3 at twenty facets. -/

namespace Kalai5.A16

theorem famT3_check : famT3.check21 = true := by decide +kernel

theorem famT3_recs_ok0 : famT3.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT3_recs_ok1 : famT3.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT3_recs_ok2 : famT3.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT3_recs_ok3 : famT3.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT3_recs_ok4 : famT3.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT3_recs_ok5 : famT3.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT3_recs_ok6 : famT3.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT3_recs_ok7 : famT3.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT3_recs_ok8 : famT3.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT3_recs_ok9 : famT3.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT3_recs_ok10 : famT3.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT3_recs_ok11 : famT3.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT3_recs_ok12 : famT3.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT3_sub0_ok : famT3.subOK 0 = true := by decide +kernel

theorem famT3_sub1_ok : famT3.subOK 1 = true := by decide +kernel

theorem famT3_sub2_ok : famT3.subOK 2 = true := by decide +kernel

theorem famT3_sub3_ok : famT3.subOK 3 = true := by decide +kernel

theorem famT3_sub4_ok : famT3.subOK 4 = true := by decide +kernel

theorem famT3_sub5_ok : famT3.subOK 5 = true := by decide +kernel

theorem famT3_sub6_ok : famT3.subOK 6 = true := by decide +kernel

theorem famT3_sub7_ok : famT3.subOK 7 = true := by decide +kernel

theorem famT3_sub8_ok : famT3.subOK 8 = true := by decide +kernel

theorem famT3_sub9_ok : famT3.subOK 9 = true := by decide +kernel

theorem famT3_sub10_ok : famT3.subOK 10 = true := by decide +kernel

theorem famT3_sub11_ok : famT3.subOK 11 = true := by decide +kernel

theorem famT3_sub12_ok : famT3.subOK 12 = true := by decide +kernel

theorem famT3_sub13_ok : famT3.subOK 13 = true := by decide +kernel

theorem famT3_sub14_ok : famT3.subOK 14 = true := by decide +kernel

theorem famT3_sub15_ok : famT3.subOK 15 = true := by decide +kernel

theorem famT3_sub16_ok : famT3.subOK 16 = true := by decide +kernel

theorem famT3_sub17_ok : famT3.subOK 17 = true := by decide +kernel

theorem famT3_sub18_ok : famT3.subOK 18 = true := by decide +kernel

theorem famT3_sub19_ok : famT3.subOK 19 = true := by decide +kernel

theorem famT3_sub20_ok : famT3.subOK 20 = true := by decide +kernel

theorem famT3_sub21_ok : famT3.subOK 21 = true := by decide +kernel

theorem famT3_sub22_ok : famT3.subOK 22 = true := by decide +kernel

theorem famT3_sub23_ok : famT3.subOK 23 = true := by decide +kernel

theorem famT3_sub24_ok : famT3.subOK 24 = true := by decide +kernel

theorem famT3_sub25_ok : famT3.subOK 25 = true := by decide +kernel

theorem famT3_sub26_ok : famT3.subOK 26 = true := by decide +kernel

theorem famT3_sub27_ok : famT3.subOK 27 = true := by decide +kernel

theorem famT3_sub28_ok : famT3.subOK 28 = true := by decide +kernel

theorem famT3_sub29_ok : famT3.subOK 29 = true := by decide +kernel

theorem famT3_sub30_ok : famT3.subOK 30 = true := by decide +kernel

theorem famT3_sub31_ok : famT3.subOK 31 = true := by decide +kernel

theorem famT3_sub32_ok : famT3.subOK 32 = true := by decide +kernel

theorem famT3_sub33_ok : famT3.subOK 33 = true := by decide +kernel

theorem famT3_sub34_ok : famT3.subOK 34 = true := by decide +kernel

theorem famT3_sub35_ok : famT3.subOK 35 = true := by decide +kernel

theorem famT3_sub36_ok : famT3.subOK 36 = true := by decide +kernel

theorem famT3_sub37_ok : famT3.subOK 37 = true := by decide +kernel

theorem famT3_sub38_ok : famT3.subOK 38 = true := by decide +kernel

theorem famT3_sub39_ok : famT3.subOK 39 = true := by decide +kernel

theorem famT3_sub40_ok : famT3.subOK 40 = true := by decide +kernel

theorem famT3_sub41_ok : famT3.subOK 41 = true := by decide +kernel

theorem famT3_sub42_ok : famT3.subOK 42 = true := by decide +kernel

theorem famT3_sub43_ok : famT3.subOK 43 = true := by decide +kernel

theorem famT3_sub44_ok : famT3.subOK 44 = true := by decide +kernel

theorem famT3_sub45_ok : famT3.subOK 45 = true := by decide +kernel

theorem famT3_sub46_ok : famT3.subOK 46 = true := by decide +kernel

theorem famT3_sub47_ok : famT3.subOK 47 = true := by decide +kernel

theorem famT3_sub48_ok : famT3.subOK 48 = true := by decide +kernel

theorem famT3_sub49_ok : famT3.subOK 49 = true := by decide +kernel

theorem famT3_sub50_ok : famT3.subOK 50 = true := by decide +kernel

theorem famT3_recs : ∀ r ∈ famT3.recs, famT3.recOK r = true :=
  famT3.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [famT3_recs_ok0, famT3_recs_ok1, famT3_recs_ok2, famT3_recs_ok3, famT3_recs_ok4, famT3_recs_ok5, famT3_recs_ok6, famT3_recs_ok7, famT3_recs_ok8, famT3_recs_ok9, famT3_recs_ok10, famT3_recs_ok11, famT3_recs_ok12])
    (by decide +kernel)

theorem famT3_subs : ∀ k < famT3.subs.length, famT3.subOK k = true := by
  intro k hk
  have h : famT3.subs.length = 51 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT3_sub0_ok, famT3_sub1_ok, famT3_sub2_ok, famT3_sub3_ok, famT3_sub4_ok, famT3_sub5_ok, famT3_sub6_ok, famT3_sub7_ok, famT3_sub8_ok, famT3_sub9_ok, famT3_sub10_ok, famT3_sub11_ok, famT3_sub12_ok, famT3_sub13_ok, famT3_sub14_ok, famT3_sub15_ok, famT3_sub16_ok, famT3_sub17_ok, famT3_sub18_ok, famT3_sub19_ok, famT3_sub20_ok, famT3_sub21_ok, famT3_sub22_ok, famT3_sub23_ok, famT3_sub24_ok, famT3_sub25_ok, famT3_sub26_ok, famT3_sub27_ok, famT3_sub28_ok, famT3_sub29_ok, famT3_sub30_ok, famT3_sub31_ok, famT3_sub32_ok, famT3_sub33_ok, famT3_sub34_ok, famT3_sub35_ok, famT3_sub36_ok, famT3_sub37_ok, famT3_sub38_ok, famT3_sub39_ok, famT3_sub40_ok, famT3_sub41_ok, famT3_sub42_ok, famT3_sub43_ok, famT3_sub44_ok, famT3_sub45_ok, famT3_sub46_ok, famT3_sub47_ok, famT3_sub48_ok, famT3_sub49_ok, famT3_sub50_ok]

end Kalai5.A16
