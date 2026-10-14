import Kalai5.A16.Data20.Fam39
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 39 at twenty facets. -/

namespace Kalai5.A16

theorem famT39_check : famT39.check21 = true := by decide +kernel

theorem famT39_recs_ok0 : famT39.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT39_recs_ok1 : famT39.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT39_recs_ok2 : famT39.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT39_recs_ok3 : famT39.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT39_recs_ok4 : famT39.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT39_recs_ok5 : famT39.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT39_recs_ok6 : famT39.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT39_recs_ok7 : famT39.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT39_recs_ok8 : famT39.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT39_recs_ok9 : famT39.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT39_recs_ok10 : famT39.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT39_recs_ok11 : famT39.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT39_recs_ok12 : famT39.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT39_sub0_ok : famT39.subOK 0 = true := by decide +kernel

theorem famT39_sub1_ok : famT39.subOK 1 = true := by decide +kernel

theorem famT39_sub2_ok : famT39.subOK 2 = true := by decide +kernel

theorem famT39_sub3_ok : famT39.subOK 3 = true := by decide +kernel

theorem famT39_sub4_ok : famT39.subOK 4 = true := by decide +kernel

theorem famT39_sub5_ok : famT39.subOK 5 = true := by decide +kernel

theorem famT39_sub6_ok : famT39.subOK 6 = true := by decide +kernel

theorem famT39_sub7_ok : famT39.subOK 7 = true := by decide +kernel

theorem famT39_sub8_ok : famT39.subOK 8 = true := by decide +kernel

theorem famT39_sub9_ok : famT39.subOK 9 = true := by decide +kernel

theorem famT39_sub10_ok : famT39.subOK 10 = true := by decide +kernel

theorem famT39_sub11_ok : famT39.subOK 11 = true := by decide +kernel

theorem famT39_sub12_ok : famT39.subOK 12 = true := by decide +kernel

theorem famT39_sub13_ok : famT39.subOK 13 = true := by decide +kernel

theorem famT39_sub14_ok : famT39.subOK 14 = true := by decide +kernel

theorem famT39_sub15_ok : famT39.subOK 15 = true := by decide +kernel

theorem famT39_sub16_ok : famT39.subOK 16 = true := by decide +kernel

theorem famT39_sub17_ok : famT39.subOK 17 = true := by decide +kernel

theorem famT39_sub18_ok : famT39.subOK 18 = true := by decide +kernel

theorem famT39_sub19_ok : famT39.subOK 19 = true := by decide +kernel

theorem famT39_sub20_ok : famT39.subOK 20 = true := by decide +kernel

theorem famT39_sub21_ok : famT39.subOK 21 = true := by decide +kernel

theorem famT39_sub22_ok : famT39.subOK 22 = true := by decide +kernel

theorem famT39_sub23_ok : famT39.subOK 23 = true := by decide +kernel

theorem famT39_sub24_ok : famT39.subOK 24 = true := by decide +kernel

theorem famT39_sub25_ok : famT39.subOK 25 = true := by decide +kernel

theorem famT39_sub26_ok : famT39.subOK 26 = true := by decide +kernel

theorem famT39_sub27_ok : famT39.subOK 27 = true := by decide +kernel

theorem famT39_sub28_ok : famT39.subOK 28 = true := by decide +kernel

theorem famT39_sub29_ok : famT39.subOK 29 = true := by decide +kernel

theorem famT39_sub30_ok : famT39.subOK 30 = true := by decide +kernel

theorem famT39_sub31_ok : famT39.subOK 31 = true := by decide +kernel

theorem famT39_sub32_ok : famT39.subOK 32 = true := by decide +kernel

theorem famT39_sub33_ok : famT39.subOK 33 = true := by decide +kernel

theorem famT39_sub34_ok : famT39.subOK 34 = true := by decide +kernel

theorem famT39_sub35_ok : famT39.subOK 35 = true := by decide +kernel

theorem famT39_sub36_ok : famT39.subOK 36 = true := by decide +kernel

theorem famT39_sub37_ok : famT39.subOK 37 = true := by decide +kernel

theorem famT39_sub38_ok : famT39.subOK 38 = true := by decide +kernel

theorem famT39_sub39_ok : famT39.subOK 39 = true := by decide +kernel

theorem famT39_sub40_ok : famT39.subOK 40 = true := by decide +kernel

theorem famT39_sub41_ok : famT39.subOK 41 = true := by decide +kernel

theorem famT39_sub42_ok : famT39.subOK 42 = true := by decide +kernel

theorem famT39_sub43_ok : famT39.subOK 43 = true := by decide +kernel

theorem famT39_sub44_ok : famT39.subOK 44 = true := by decide +kernel

theorem famT39_sub45_ok : famT39.subOK 45 = true := by decide +kernel

theorem famT39_sub46_ok : famT39.subOK 46 = true := by decide +kernel

theorem famT39_sub47_ok : famT39.subOK 47 = true := by decide +kernel

theorem famT39_sub48_ok : famT39.subOK 48 = true := by decide +kernel

theorem famT39_sub49_ok : famT39.subOK 49 = true := by decide +kernel

theorem famT39_sub50_ok : famT39.subOK 50 = true := by decide +kernel

theorem famT39_recs : ∀ r ∈ famT39.recs, famT39.recOK r = true :=
  famT39.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [famT39_recs_ok0, famT39_recs_ok1, famT39_recs_ok2, famT39_recs_ok3, famT39_recs_ok4, famT39_recs_ok5, famT39_recs_ok6, famT39_recs_ok7, famT39_recs_ok8, famT39_recs_ok9, famT39_recs_ok10, famT39_recs_ok11, famT39_recs_ok12])
    (by decide +kernel)

theorem famT39_subs : ∀ k < famT39.subs.length, famT39.subOK k = true := by
  intro k hk
  have h : famT39.subs.length = 51 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT39_sub0_ok, famT39_sub1_ok, famT39_sub2_ok, famT39_sub3_ok, famT39_sub4_ok, famT39_sub5_ok, famT39_sub6_ok, famT39_sub7_ok, famT39_sub8_ok, famT39_sub9_ok, famT39_sub10_ok, famT39_sub11_ok, famT39_sub12_ok, famT39_sub13_ok, famT39_sub14_ok, famT39_sub15_ok, famT39_sub16_ok, famT39_sub17_ok, famT39_sub18_ok, famT39_sub19_ok, famT39_sub20_ok, famT39_sub21_ok, famT39_sub22_ok, famT39_sub23_ok, famT39_sub24_ok, famT39_sub25_ok, famT39_sub26_ok, famT39_sub27_ok, famT39_sub28_ok, famT39_sub29_ok, famT39_sub30_ok, famT39_sub31_ok, famT39_sub32_ok, famT39_sub33_ok, famT39_sub34_ok, famT39_sub35_ok, famT39_sub36_ok, famT39_sub37_ok, famT39_sub38_ok, famT39_sub39_ok, famT39_sub40_ok, famT39_sub41_ok, famT39_sub42_ok, famT39_sub43_ok, famT39_sub44_ok, famT39_sub45_ok, famT39_sub46_ok, famT39_sub47_ok, famT39_sub48_ok, famT39_sub49_ok, famT39_sub50_ok]

end Kalai5.A16
