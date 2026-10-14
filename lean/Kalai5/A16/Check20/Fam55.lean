import Kalai5.A16.Data20.Fam55
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 55 at twenty facets. -/

namespace Kalai5.A16

theorem famT55_check : famT55.check21 = true := by decide +kernel

theorem famT55_recs_ok0 : famT55.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT55_recs_ok1 : famT55.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT55_recs_ok2 : famT55.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT55_recs_ok3 : famT55.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT55_recs_ok4 : famT55.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT55_recs_ok5 : famT55.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT55_recs_ok6 : famT55.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT55_recs_ok7 : famT55.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT55_recs_ok8 : famT55.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT55_recs_ok9 : famT55.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT55_recs_ok10 : famT55.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT55_recs_ok11 : famT55.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT55_recs_ok12 : famT55.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT55_sub0_ok : famT55.subOK 0 = true := by decide +kernel

theorem famT55_sub1_ok : famT55.subOK 1 = true := by decide +kernel

theorem famT55_sub2_ok : famT55.subOK 2 = true := by decide +kernel

theorem famT55_sub3_ok : famT55.subOK 3 = true := by decide +kernel

theorem famT55_sub4_ok : famT55.subOK 4 = true := by decide +kernel

theorem famT55_sub5_ok : famT55.subOK 5 = true := by decide +kernel

theorem famT55_sub6_ok : famT55.subOK 6 = true := by decide +kernel

theorem famT55_sub7_ok : famT55.subOK 7 = true := by decide +kernel

theorem famT55_sub8_ok : famT55.subOK 8 = true := by decide +kernel

theorem famT55_sub9_ok : famT55.subOK 9 = true := by decide +kernel

theorem famT55_sub10_ok : famT55.subOK 10 = true := by decide +kernel

theorem famT55_sub11_ok : famT55.subOK 11 = true := by decide +kernel

theorem famT55_sub12_ok : famT55.subOK 12 = true := by decide +kernel

theorem famT55_sub13_ok : famT55.subOK 13 = true := by decide +kernel

theorem famT55_sub14_ok : famT55.subOK 14 = true := by decide +kernel

theorem famT55_sub15_ok : famT55.subOK 15 = true := by decide +kernel

theorem famT55_sub16_ok : famT55.subOK 16 = true := by decide +kernel

theorem famT55_sub17_ok : famT55.subOK 17 = true := by decide +kernel

theorem famT55_sub18_ok : famT55.subOK 18 = true := by decide +kernel

theorem famT55_sub19_ok : famT55.subOK 19 = true := by decide +kernel

theorem famT55_sub20_ok : famT55.subOK 20 = true := by decide +kernel

theorem famT55_sub21_ok : famT55.subOK 21 = true := by decide +kernel

theorem famT55_sub22_ok : famT55.subOK 22 = true := by decide +kernel

theorem famT55_sub23_ok : famT55.subOK 23 = true := by decide +kernel

theorem famT55_sub24_ok : famT55.subOK 24 = true := by decide +kernel

theorem famT55_sub25_ok : famT55.subOK 25 = true := by decide +kernel

theorem famT55_sub26_ok : famT55.subOK 26 = true := by decide +kernel

theorem famT55_sub27_ok : famT55.subOK 27 = true := by decide +kernel

theorem famT55_sub28_ok : famT55.subOK 28 = true := by decide +kernel

theorem famT55_sub29_ok : famT55.subOK 29 = true := by decide +kernel

theorem famT55_sub30_ok : famT55.subOK 30 = true := by decide +kernel

theorem famT55_sub31_ok : famT55.subOK 31 = true := by decide +kernel

theorem famT55_sub32_ok : famT55.subOK 32 = true := by decide +kernel

theorem famT55_sub33_ok : famT55.subOK 33 = true := by decide +kernel

theorem famT55_sub34_ok : famT55.subOK 34 = true := by decide +kernel

theorem famT55_sub35_ok : famT55.subOK 35 = true := by decide +kernel

theorem famT55_sub36_ok : famT55.subOK 36 = true := by decide +kernel

theorem famT55_sub37_ok : famT55.subOK 37 = true := by decide +kernel

theorem famT55_sub38_ok : famT55.subOK 38 = true := by decide +kernel

theorem famT55_sub39_ok : famT55.subOK 39 = true := by decide +kernel

theorem famT55_sub40_ok : famT55.subOK 40 = true := by decide +kernel

theorem famT55_sub41_ok : famT55.subOK 41 = true := by decide +kernel

theorem famT55_sub42_ok : famT55.subOK 42 = true := by decide +kernel

theorem famT55_sub43_ok : famT55.subOK 43 = true := by decide +kernel

theorem famT55_sub44_ok : famT55.subOK 44 = true := by decide +kernel

theorem famT55_sub45_ok : famT55.subOK 45 = true := by decide +kernel

theorem famT55_sub46_ok : famT55.subOK 46 = true := by decide +kernel

theorem famT55_sub47_ok : famT55.subOK 47 = true := by decide +kernel

theorem famT55_sub48_ok : famT55.subOK 48 = true := by decide +kernel

theorem famT55_sub49_ok : famT55.subOK 49 = true := by decide +kernel

theorem famT55_sub50_ok : famT55.subOK 50 = true := by decide +kernel

theorem famT55_recs : ∀ r ∈ famT55.recs, famT55.recOK r = true :=
  famT55.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [famT55_recs_ok0, famT55_recs_ok1, famT55_recs_ok2, famT55_recs_ok3, famT55_recs_ok4, famT55_recs_ok5, famT55_recs_ok6, famT55_recs_ok7, famT55_recs_ok8, famT55_recs_ok9, famT55_recs_ok10, famT55_recs_ok11, famT55_recs_ok12])
    (by decide +kernel)

theorem famT55_subs : ∀ k < famT55.subs.length, famT55.subOK k = true := by
  intro k hk
  have h : famT55.subs.length = 51 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT55_sub0_ok, famT55_sub1_ok, famT55_sub2_ok, famT55_sub3_ok, famT55_sub4_ok, famT55_sub5_ok, famT55_sub6_ok, famT55_sub7_ok, famT55_sub8_ok, famT55_sub9_ok, famT55_sub10_ok, famT55_sub11_ok, famT55_sub12_ok, famT55_sub13_ok, famT55_sub14_ok, famT55_sub15_ok, famT55_sub16_ok, famT55_sub17_ok, famT55_sub18_ok, famT55_sub19_ok, famT55_sub20_ok, famT55_sub21_ok, famT55_sub22_ok, famT55_sub23_ok, famT55_sub24_ok, famT55_sub25_ok, famT55_sub26_ok, famT55_sub27_ok, famT55_sub28_ok, famT55_sub29_ok, famT55_sub30_ok, famT55_sub31_ok, famT55_sub32_ok, famT55_sub33_ok, famT55_sub34_ok, famT55_sub35_ok, famT55_sub36_ok, famT55_sub37_ok, famT55_sub38_ok, famT55_sub39_ok, famT55_sub40_ok, famT55_sub41_ok, famT55_sub42_ok, famT55_sub43_ok, famT55_sub44_ok, famT55_sub45_ok, famT55_sub46_ok, famT55_sub47_ok, famT55_sub48_ok, famT55_sub49_ok, famT55_sub50_ok]

end Kalai5.A16
