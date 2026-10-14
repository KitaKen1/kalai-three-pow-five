import Kalai5.A16.Data20.Fam24
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 24 at twenty facets. -/

namespace Kalai5.A16

theorem famT24_check : famT24.check21 = true := by decide +kernel

theorem famT24_recs_ok0 : famT24.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT24_recs_ok1 : famT24.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT24_recs_ok2 : famT24.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT24_recs_ok3 : famT24.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT24_recs_ok4 : famT24.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT24_recs_ok5 : famT24.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT24_recs_ok6 : famT24.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT24_recs_ok7 : famT24.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT24_recs_ok8 : famT24.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT24_recs_ok9 : famT24.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT24_recs_ok10 : famT24.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT24_recs_ok11 : famT24.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT24_recs_ok12 : famT24.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT24_sub0_ok : famT24.subOK 0 = true := by decide +kernel

theorem famT24_sub1_ok : famT24.subOK 1 = true := by decide +kernel

theorem famT24_sub2_ok : famT24.subOK 2 = true := by decide +kernel

theorem famT24_sub3_ok : famT24.subOK 3 = true := by decide +kernel

theorem famT24_sub4_ok : famT24.subOK 4 = true := by decide +kernel

theorem famT24_sub5_ok : famT24.subOK 5 = true := by decide +kernel

theorem famT24_sub6_ok : famT24.subOK 6 = true := by decide +kernel

theorem famT24_sub7_ok : famT24.subOK 7 = true := by decide +kernel

theorem famT24_sub8_ok : famT24.subOK 8 = true := by decide +kernel

theorem famT24_sub9_ok : famT24.subOK 9 = true := by decide +kernel

theorem famT24_sub10_ok : famT24.subOK 10 = true := by decide +kernel

theorem famT24_sub11_ok : famT24.subOK 11 = true := by decide +kernel

theorem famT24_sub12_ok : famT24.subOK 12 = true := by decide +kernel

theorem famT24_sub13_ok : famT24.subOK 13 = true := by decide +kernel

theorem famT24_sub14_ok : famT24.subOK 14 = true := by decide +kernel

theorem famT24_sub15_ok : famT24.subOK 15 = true := by decide +kernel

theorem famT24_sub16_ok : famT24.subOK 16 = true := by decide +kernel

theorem famT24_sub17_ok : famT24.subOK 17 = true := by decide +kernel

theorem famT24_sub18_ok : famT24.subOK 18 = true := by decide +kernel

theorem famT24_sub19_ok : famT24.subOK 19 = true := by decide +kernel

theorem famT24_sub20_ok : famT24.subOK 20 = true := by decide +kernel

theorem famT24_sub21_ok : famT24.subOK 21 = true := by decide +kernel

theorem famT24_sub22_ok : famT24.subOK 22 = true := by decide +kernel

theorem famT24_sub23_ok : famT24.subOK 23 = true := by decide +kernel

theorem famT24_sub24_ok : famT24.subOK 24 = true := by decide +kernel

theorem famT24_sub25_ok : famT24.subOK 25 = true := by decide +kernel

theorem famT24_sub26_ok : famT24.subOK 26 = true := by decide +kernel

theorem famT24_sub27_ok : famT24.subOK 27 = true := by decide +kernel

theorem famT24_sub28_ok : famT24.subOK 28 = true := by decide +kernel

theorem famT24_sub29_ok : famT24.subOK 29 = true := by decide +kernel

theorem famT24_sub30_ok : famT24.subOK 30 = true := by decide +kernel

theorem famT24_sub31_ok : famT24.subOK 31 = true := by decide +kernel

theorem famT24_sub32_ok : famT24.subOK 32 = true := by decide +kernel

theorem famT24_sub33_ok : famT24.subOK 33 = true := by decide +kernel

theorem famT24_sub34_ok : famT24.subOK 34 = true := by decide +kernel

theorem famT24_sub35_ok : famT24.subOK 35 = true := by decide +kernel

theorem famT24_sub36_ok : famT24.subOK 36 = true := by decide +kernel

theorem famT24_sub37_ok : famT24.subOK 37 = true := by decide +kernel

theorem famT24_sub38_ok : famT24.subOK 38 = true := by decide +kernel

theorem famT24_recs : ∀ r ∈ famT24.recs, famT24.recOK r = true :=
  famT24.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [famT24_recs_ok0, famT24_recs_ok1, famT24_recs_ok2, famT24_recs_ok3, famT24_recs_ok4, famT24_recs_ok5, famT24_recs_ok6, famT24_recs_ok7, famT24_recs_ok8, famT24_recs_ok9, famT24_recs_ok10, famT24_recs_ok11, famT24_recs_ok12])
    (by decide +kernel)

theorem famT24_subs : ∀ k < famT24.subs.length, famT24.subOK k = true := by
  intro k hk
  have h : famT24.subs.length = 39 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT24_sub0_ok, famT24_sub1_ok, famT24_sub2_ok, famT24_sub3_ok, famT24_sub4_ok, famT24_sub5_ok, famT24_sub6_ok, famT24_sub7_ok, famT24_sub8_ok, famT24_sub9_ok, famT24_sub10_ok, famT24_sub11_ok, famT24_sub12_ok, famT24_sub13_ok, famT24_sub14_ok, famT24_sub15_ok, famT24_sub16_ok, famT24_sub17_ok, famT24_sub18_ok, famT24_sub19_ok, famT24_sub20_ok, famT24_sub21_ok, famT24_sub22_ok, famT24_sub23_ok, famT24_sub24_ok, famT24_sub25_ok, famT24_sub26_ok, famT24_sub27_ok, famT24_sub28_ok, famT24_sub29_ok, famT24_sub30_ok, famT24_sub31_ok, famT24_sub32_ok, famT24_sub33_ok, famT24_sub34_ok, famT24_sub35_ok, famT24_sub36_ok, famT24_sub37_ok, famT24_sub38_ok]

end Kalai5.A16
