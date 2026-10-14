import Kalai5.A16.Data20.Fam38
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 38 at twenty facets. -/

namespace Kalai5.A16

theorem famT38_check : famT38.check21 = true := by decide +kernel

theorem famT38_recs_ok0 : famT38.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT38_recs_ok1 : famT38.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT38_recs_ok2 : famT38.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT38_recs_ok3 : famT38.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT38_recs_ok4 : famT38.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT38_recs_ok5 : famT38.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT38_recs_ok6 : famT38.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT38_recs_ok7 : famT38.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT38_recs_ok8 : famT38.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT38_recs_ok9 : famT38.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT38_recs_ok10 : famT38.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT38_recs_ok11 : famT38.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT38_sub0_ok : famT38.subOK 0 = true := by decide +kernel

theorem famT38_sub1_ok : famT38.subOK 1 = true := by decide +kernel

theorem famT38_sub2_ok : famT38.subOK 2 = true := by decide +kernel

theorem famT38_sub3_ok : famT38.subOK 3 = true := by decide +kernel

theorem famT38_sub4_ok : famT38.subOK 4 = true := by decide +kernel

theorem famT38_sub5_ok : famT38.subOK 5 = true := by decide +kernel

theorem famT38_sub6_ok : famT38.subOK 6 = true := by decide +kernel

theorem famT38_sub7_ok : famT38.subOK 7 = true := by decide +kernel

theorem famT38_sub8_ok : famT38.subOK 8 = true := by decide +kernel

theorem famT38_sub9_ok : famT38.subOK 9 = true := by decide +kernel

theorem famT38_sub10_ok : famT38.subOK 10 = true := by decide +kernel

theorem famT38_sub11_ok : famT38.subOK 11 = true := by decide +kernel

theorem famT38_sub12_ok : famT38.subOK 12 = true := by decide +kernel

theorem famT38_sub13_ok : famT38.subOK 13 = true := by decide +kernel

theorem famT38_sub14_ok : famT38.subOK 14 = true := by decide +kernel

theorem famT38_sub15_ok : famT38.subOK 15 = true := by decide +kernel

theorem famT38_sub16_ok : famT38.subOK 16 = true := by decide +kernel

theorem famT38_sub17_ok : famT38.subOK 17 = true := by decide +kernel

theorem famT38_sub18_ok : famT38.subOK 18 = true := by decide +kernel

theorem famT38_sub19_ok : famT38.subOK 19 = true := by decide +kernel

theorem famT38_sub20_ok : famT38.subOK 20 = true := by decide +kernel

theorem famT38_sub21_ok : famT38.subOK 21 = true := by decide +kernel

theorem famT38_sub22_ok : famT38.subOK 22 = true := by decide +kernel

theorem famT38_sub23_ok : famT38.subOK 23 = true := by decide +kernel

theorem famT38_sub24_ok : famT38.subOK 24 = true := by decide +kernel

theorem famT38_sub25_ok : famT38.subOK 25 = true := by decide +kernel

theorem famT38_sub26_ok : famT38.subOK 26 = true := by decide +kernel

theorem famT38_sub27_ok : famT38.subOK 27 = true := by decide +kernel

theorem famT38_sub28_ok : famT38.subOK 28 = true := by decide +kernel

theorem famT38_sub29_ok : famT38.subOK 29 = true := by decide +kernel

theorem famT38_sub30_ok : famT38.subOK 30 = true := by decide +kernel

theorem famT38_sub31_ok : famT38.subOK 31 = true := by decide +kernel

theorem famT38_sub32_ok : famT38.subOK 32 = true := by decide +kernel

theorem famT38_sub33_ok : famT38.subOK 33 = true := by decide +kernel

theorem famT38_sub34_ok : famT38.subOK 34 = true := by decide +kernel

theorem famT38_sub35_ok : famT38.subOK 35 = true := by decide +kernel

theorem famT38_sub36_ok : famT38.subOK 36 = true := by decide +kernel

theorem famT38_sub37_ok : famT38.subOK 37 = true := by decide +kernel

theorem famT38_sub38_ok : famT38.subOK 38 = true := by decide +kernel

theorem famT38_sub39_ok : famT38.subOK 39 = true := by decide +kernel

theorem famT38_sub40_ok : famT38.subOK 40 = true := by decide +kernel

theorem famT38_sub41_ok : famT38.subOK 41 = true := by decide +kernel

theorem famT38_sub42_ok : famT38.subOK 42 = true := by decide +kernel

theorem famT38_sub43_ok : famT38.subOK 43 = true := by decide +kernel

theorem famT38_sub44_ok : famT38.subOK 44 = true := by decide +kernel

theorem famT38_sub45_ok : famT38.subOK 45 = true := by decide +kernel

theorem famT38_sub46_ok : famT38.subOK 46 = true := by decide +kernel

theorem famT38_sub47_ok : famT38.subOK 47 = true := by decide +kernel

theorem famT38_sub48_ok : famT38.subOK 48 = true := by decide +kernel

theorem famT38_sub49_ok : famT38.subOK 49 = true := by decide +kernel

theorem famT38_sub50_ok : famT38.subOK 50 = true := by decide +kernel

theorem famT38_recs : ∀ r ∈ famT38.recs, famT38.recOK r = true :=
  famT38.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [famT38_recs_ok0, famT38_recs_ok1, famT38_recs_ok2, famT38_recs_ok3, famT38_recs_ok4, famT38_recs_ok5, famT38_recs_ok6, famT38_recs_ok7, famT38_recs_ok8, famT38_recs_ok9, famT38_recs_ok10, famT38_recs_ok11])
    (by decide +kernel)

theorem famT38_subs : ∀ k < famT38.subs.length, famT38.subOK k = true := by
  intro k hk
  have h : famT38.subs.length = 51 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT38_sub0_ok, famT38_sub1_ok, famT38_sub2_ok, famT38_sub3_ok, famT38_sub4_ok, famT38_sub5_ok, famT38_sub6_ok, famT38_sub7_ok, famT38_sub8_ok, famT38_sub9_ok, famT38_sub10_ok, famT38_sub11_ok, famT38_sub12_ok, famT38_sub13_ok, famT38_sub14_ok, famT38_sub15_ok, famT38_sub16_ok, famT38_sub17_ok, famT38_sub18_ok, famT38_sub19_ok, famT38_sub20_ok, famT38_sub21_ok, famT38_sub22_ok, famT38_sub23_ok, famT38_sub24_ok, famT38_sub25_ok, famT38_sub26_ok, famT38_sub27_ok, famT38_sub28_ok, famT38_sub29_ok, famT38_sub30_ok, famT38_sub31_ok, famT38_sub32_ok, famT38_sub33_ok, famT38_sub34_ok, famT38_sub35_ok, famT38_sub36_ok, famT38_sub37_ok, famT38_sub38_ok, famT38_sub39_ok, famT38_sub40_ok, famT38_sub41_ok, famT38_sub42_ok, famT38_sub43_ok, famT38_sub44_ok, famT38_sub45_ok, famT38_sub46_ok, famT38_sub47_ok, famT38_sub48_ok, famT38_sub49_ok, famT38_sub50_ok]

end Kalai5.A16
