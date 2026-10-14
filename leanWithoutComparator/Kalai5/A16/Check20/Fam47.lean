import Kalai5.A16.Data20.Fam47
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 47 at twenty facets. -/

namespace Kalai5.A16

theorem famT47_check : famT47.check21 = true := by decide +kernel

theorem famT47_recs_ok0 : famT47.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT47_recs_ok1 : famT47.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT47_recs_ok2 : famT47.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT47_recs_ok3 : famT47.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT47_recs_ok4 : famT47.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT47_recs_ok5 : famT47.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT47_recs_ok6 : famT47.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT47_recs_ok7 : famT47.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT47_recs_ok8 : famT47.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT47_recs_ok9 : famT47.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT47_recs_ok10 : famT47.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT47_recs_ok11 : famT47.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT47_recs_ok12 : famT47.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT47_sub0_ok : famT47.subOK 0 = true := by decide +kernel

theorem famT47_sub1_ok : famT47.subOK 1 = true := by decide +kernel

theorem famT47_sub2_ok : famT47.subOK 2 = true := by decide +kernel

theorem famT47_sub3_ok : famT47.subOK 3 = true := by decide +kernel

theorem famT47_sub4_ok : famT47.subOK 4 = true := by decide +kernel

theorem famT47_sub5_ok : famT47.subOK 5 = true := by decide +kernel

theorem famT47_sub6_ok : famT47.subOK 6 = true := by decide +kernel

theorem famT47_sub7_ok : famT47.subOK 7 = true := by decide +kernel

theorem famT47_sub8_ok : famT47.subOK 8 = true := by decide +kernel

theorem famT47_sub9_ok : famT47.subOK 9 = true := by decide +kernel

theorem famT47_sub10_ok : famT47.subOK 10 = true := by decide +kernel

theorem famT47_sub11_ok : famT47.subOK 11 = true := by decide +kernel

theorem famT47_sub12_ok : famT47.subOK 12 = true := by decide +kernel

theorem famT47_sub13_ok : famT47.subOK 13 = true := by decide +kernel

theorem famT47_sub14_ok : famT47.subOK 14 = true := by decide +kernel

theorem famT47_sub15_ok : famT47.subOK 15 = true := by decide +kernel

theorem famT47_sub16_ok : famT47.subOK 16 = true := by decide +kernel

theorem famT47_sub17_ok : famT47.subOK 17 = true := by decide +kernel

theorem famT47_sub18_ok : famT47.subOK 18 = true := by decide +kernel

theorem famT47_sub19_ok : famT47.subOK 19 = true := by decide +kernel

theorem famT47_sub20_ok : famT47.subOK 20 = true := by decide +kernel

theorem famT47_sub21_ok : famT47.subOK 21 = true := by decide +kernel

theorem famT47_sub22_ok : famT47.subOK 22 = true := by decide +kernel

theorem famT47_sub23_ok : famT47.subOK 23 = true := by decide +kernel

theorem famT47_sub24_ok : famT47.subOK 24 = true := by decide +kernel

theorem famT47_sub25_ok : famT47.subOK 25 = true := by decide +kernel

theorem famT47_sub26_ok : famT47.subOK 26 = true := by decide +kernel

theorem famT47_sub27_ok : famT47.subOK 27 = true := by decide +kernel

theorem famT47_sub28_ok : famT47.subOK 28 = true := by decide +kernel

theorem famT47_sub29_ok : famT47.subOK 29 = true := by decide +kernel

theorem famT47_sub30_ok : famT47.subOK 30 = true := by decide +kernel

theorem famT47_sub31_ok : famT47.subOK 31 = true := by decide +kernel

theorem famT47_sub32_ok : famT47.subOK 32 = true := by decide +kernel

theorem famT47_sub33_ok : famT47.subOK 33 = true := by decide +kernel

theorem famT47_sub34_ok : famT47.subOK 34 = true := by decide +kernel

theorem famT47_sub35_ok : famT47.subOK 35 = true := by decide +kernel

theorem famT47_sub36_ok : famT47.subOK 36 = true := by decide +kernel

theorem famT47_sub37_ok : famT47.subOK 37 = true := by decide +kernel

theorem famT47_sub38_ok : famT47.subOK 38 = true := by decide +kernel

theorem famT47_sub39_ok : famT47.subOK 39 = true := by decide +kernel

theorem famT47_sub40_ok : famT47.subOK 40 = true := by decide +kernel

theorem famT47_sub41_ok : famT47.subOK 41 = true := by decide +kernel

theorem famT47_sub42_ok : famT47.subOK 42 = true := by decide +kernel

theorem famT47_recs : ∀ r ∈ famT47.recs, famT47.recOK r = true :=
  famT47.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [famT47_recs_ok0, famT47_recs_ok1, famT47_recs_ok2, famT47_recs_ok3, famT47_recs_ok4, famT47_recs_ok5, famT47_recs_ok6, famT47_recs_ok7, famT47_recs_ok8, famT47_recs_ok9, famT47_recs_ok10, famT47_recs_ok11, famT47_recs_ok12])
    (by decide +kernel)

theorem famT47_subs : ∀ k < famT47.subs.length, famT47.subOK k = true := by
  intro k hk
  have h : famT47.subs.length = 43 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT47_sub0_ok, famT47_sub1_ok, famT47_sub2_ok, famT47_sub3_ok, famT47_sub4_ok, famT47_sub5_ok, famT47_sub6_ok, famT47_sub7_ok, famT47_sub8_ok, famT47_sub9_ok, famT47_sub10_ok, famT47_sub11_ok, famT47_sub12_ok, famT47_sub13_ok, famT47_sub14_ok, famT47_sub15_ok, famT47_sub16_ok, famT47_sub17_ok, famT47_sub18_ok, famT47_sub19_ok, famT47_sub20_ok, famT47_sub21_ok, famT47_sub22_ok, famT47_sub23_ok, famT47_sub24_ok, famT47_sub25_ok, famT47_sub26_ok, famT47_sub27_ok, famT47_sub28_ok, famT47_sub29_ok, famT47_sub30_ok, famT47_sub31_ok, famT47_sub32_ok, famT47_sub33_ok, famT47_sub34_ok, famT47_sub35_ok, famT47_sub36_ok, famT47_sub37_ok, famT47_sub38_ok, famT47_sub39_ok, famT47_sub40_ok, famT47_sub41_ok, famT47_sub42_ok]

end Kalai5.A16
