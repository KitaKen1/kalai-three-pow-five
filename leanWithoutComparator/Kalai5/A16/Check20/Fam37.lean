import Kalai5.A16.Data20.Fam37
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 37 at twenty facets. -/

namespace Kalai5.A16

theorem famT37_check : famT37.check21 = true := by decide +kernel

theorem famT37_recs_ok0 : famT37.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT37_recs_ok1 : famT37.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT37_recs_ok2 : famT37.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT37_recs_ok3 : famT37.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT37_recs_ok4 : famT37.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT37_recs_ok5 : famT37.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT37_recs_ok6 : famT37.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT37_recs_ok7 : famT37.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT37_recs_ok8 : famT37.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT37_recs_ok9 : famT37.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT37_recs_ok10 : famT37.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT37_recs_ok11 : famT37.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT37_recs_ok12 : famT37.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT37_recs_ok13 : famT37.recsOK (40 * 13) 40 = true := by decide +kernel

theorem famT37_recs_ok14 : famT37.recsOK (40 * 14) 40 = true := by decide +kernel

theorem famT37_sub0_ok : famT37.subOK 0 = true := by decide +kernel

theorem famT37_sub1_ok : famT37.subOK 1 = true := by decide +kernel

theorem famT37_sub2_ok : famT37.subOK 2 = true := by decide +kernel

theorem famT37_sub3_ok : famT37.subOK 3 = true := by decide +kernel

theorem famT37_sub4_ok : famT37.subOK 4 = true := by decide +kernel

theorem famT37_sub5_ok : famT37.subOK 5 = true := by decide +kernel

theorem famT37_sub6_ok : famT37.subOK 6 = true := by decide +kernel

theorem famT37_sub7_ok : famT37.subOK 7 = true := by decide +kernel

theorem famT37_sub8_ok : famT37.subOK 8 = true := by decide +kernel

theorem famT37_sub9_ok : famT37.subOK 9 = true := by decide +kernel

theorem famT37_sub10_ok : famT37.subOK 10 = true := by decide +kernel

theorem famT37_sub11_ok : famT37.subOK 11 = true := by decide +kernel

theorem famT37_sub12_ok : famT37.subOK 12 = true := by decide +kernel

theorem famT37_sub13_ok : famT37.subOK 13 = true := by decide +kernel

theorem famT37_sub14_ok : famT37.subOK 14 = true := by decide +kernel

theorem famT37_sub15_ok : famT37.subOK 15 = true := by decide +kernel

theorem famT37_sub16_ok : famT37.subOK 16 = true := by decide +kernel

theorem famT37_sub17_ok : famT37.subOK 17 = true := by decide +kernel

theorem famT37_sub18_ok : famT37.subOK 18 = true := by decide +kernel

theorem famT37_sub19_ok : famT37.subOK 19 = true := by decide +kernel

theorem famT37_sub20_ok : famT37.subOK 20 = true := by decide +kernel

theorem famT37_sub21_ok : famT37.subOK 21 = true := by decide +kernel

theorem famT37_sub22_ok : famT37.subOK 22 = true := by decide +kernel

theorem famT37_sub23_ok : famT37.subOK 23 = true := by decide +kernel

theorem famT37_sub24_ok : famT37.subOK 24 = true := by decide +kernel

theorem famT37_sub25_ok : famT37.subOK 25 = true := by decide +kernel

theorem famT37_sub26_ok : famT37.subOK 26 = true := by decide +kernel

theorem famT37_sub27_ok : famT37.subOK 27 = true := by decide +kernel

theorem famT37_sub28_ok : famT37.subOK 28 = true := by decide +kernel

theorem famT37_sub29_ok : famT37.subOK 29 = true := by decide +kernel

theorem famT37_sub30_ok : famT37.subOK 30 = true := by decide +kernel

theorem famT37_sub31_ok : famT37.subOK 31 = true := by decide +kernel

theorem famT37_sub32_ok : famT37.subOK 32 = true := by decide +kernel

theorem famT37_sub33_ok : famT37.subOK 33 = true := by decide +kernel

theorem famT37_sub34_ok : famT37.subOK 34 = true := by decide +kernel

theorem famT37_sub35_ok : famT37.subOK 35 = true := by decide +kernel

theorem famT37_sub36_ok : famT37.subOK 36 = true := by decide +kernel

theorem famT37_sub37_ok : famT37.subOK 37 = true := by decide +kernel

theorem famT37_sub38_ok : famT37.subOK 38 = true := by decide +kernel

theorem famT37_sub39_ok : famT37.subOK 39 = true := by decide +kernel

theorem famT37_sub40_ok : famT37.subOK 40 = true := by decide +kernel

theorem famT37_sub41_ok : famT37.subOK 41 = true := by decide +kernel

theorem famT37_sub42_ok : famT37.subOK 42 = true := by decide +kernel

theorem famT37_recs : ∀ r ∈ famT37.recs, famT37.recOK r = true :=
  famT37.recs_of_chunks 15 (fun c hc => by
    interval_cases c
    exacts [famT37_recs_ok0, famT37_recs_ok1, famT37_recs_ok2, famT37_recs_ok3, famT37_recs_ok4, famT37_recs_ok5, famT37_recs_ok6, famT37_recs_ok7, famT37_recs_ok8, famT37_recs_ok9, famT37_recs_ok10, famT37_recs_ok11, famT37_recs_ok12, famT37_recs_ok13, famT37_recs_ok14])
    (by decide +kernel)

theorem famT37_subs : ∀ k < famT37.subs.length, famT37.subOK k = true := by
  intro k hk
  have h : famT37.subs.length = 43 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT37_sub0_ok, famT37_sub1_ok, famT37_sub2_ok, famT37_sub3_ok, famT37_sub4_ok, famT37_sub5_ok, famT37_sub6_ok, famT37_sub7_ok, famT37_sub8_ok, famT37_sub9_ok, famT37_sub10_ok, famT37_sub11_ok, famT37_sub12_ok, famT37_sub13_ok, famT37_sub14_ok, famT37_sub15_ok, famT37_sub16_ok, famT37_sub17_ok, famT37_sub18_ok, famT37_sub19_ok, famT37_sub20_ok, famT37_sub21_ok, famT37_sub22_ok, famT37_sub23_ok, famT37_sub24_ok, famT37_sub25_ok, famT37_sub26_ok, famT37_sub27_ok, famT37_sub28_ok, famT37_sub29_ok, famT37_sub30_ok, famT37_sub31_ok, famT37_sub32_ok, famT37_sub33_ok, famT37_sub34_ok, famT37_sub35_ok, famT37_sub36_ok, famT37_sub37_ok, famT37_sub38_ok, famT37_sub39_ok, famT37_sub40_ok, famT37_sub41_ok, famT37_sub42_ok]

end Kalai5.A16
