import Kalai5.A16.Data20.Fam28
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 28 at twenty facets. -/

namespace Kalai5.A16

theorem famT28_check : famT28.check21 = true := by decide +kernel

theorem famT28_recs_ok0 : famT28.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT28_recs_ok1 : famT28.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT28_recs_ok2 : famT28.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT28_recs_ok3 : famT28.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT28_recs_ok4 : famT28.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT28_recs_ok5 : famT28.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT28_recs_ok6 : famT28.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT28_recs_ok7 : famT28.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT28_recs_ok8 : famT28.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT28_recs_ok9 : famT28.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT28_recs_ok10 : famT28.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT28_recs_ok11 : famT28.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT28_recs_ok12 : famT28.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT28_sub0_ok : famT28.subOK 0 = true := by decide +kernel

theorem famT28_sub1_ok : famT28.subOK 1 = true := by decide +kernel

theorem famT28_sub2_ok : famT28.subOK 2 = true := by decide +kernel

theorem famT28_sub3_ok : famT28.subOK 3 = true := by decide +kernel

theorem famT28_sub4_ok : famT28.subOK 4 = true := by decide +kernel

theorem famT28_sub5_ok : famT28.subOK 5 = true := by decide +kernel

theorem famT28_sub6_ok : famT28.subOK 6 = true := by decide +kernel

theorem famT28_sub7_ok : famT28.subOK 7 = true := by decide +kernel

theorem famT28_sub8_ok : famT28.subOK 8 = true := by decide +kernel

theorem famT28_sub9_ok : famT28.subOK 9 = true := by decide +kernel

theorem famT28_sub10_ok : famT28.subOK 10 = true := by decide +kernel

theorem famT28_sub11_ok : famT28.subOK 11 = true := by decide +kernel

theorem famT28_sub12_ok : famT28.subOK 12 = true := by decide +kernel

theorem famT28_sub13_ok : famT28.subOK 13 = true := by decide +kernel

theorem famT28_sub14_ok : famT28.subOK 14 = true := by decide +kernel

theorem famT28_sub15_ok : famT28.subOK 15 = true := by decide +kernel

theorem famT28_sub16_ok : famT28.subOK 16 = true := by decide +kernel

theorem famT28_sub17_ok : famT28.subOK 17 = true := by decide +kernel

theorem famT28_sub18_ok : famT28.subOK 18 = true := by decide +kernel

theorem famT28_sub19_ok : famT28.subOK 19 = true := by decide +kernel

theorem famT28_sub20_ok : famT28.subOK 20 = true := by decide +kernel

theorem famT28_sub21_ok : famT28.subOK 21 = true := by decide +kernel

theorem famT28_sub22_ok : famT28.subOK 22 = true := by decide +kernel

theorem famT28_sub23_ok : famT28.subOK 23 = true := by decide +kernel

theorem famT28_sub24_ok : famT28.subOK 24 = true := by decide +kernel

theorem famT28_sub25_ok : famT28.subOK 25 = true := by decide +kernel

theorem famT28_sub26_ok : famT28.subOK 26 = true := by decide +kernel

theorem famT28_sub27_ok : famT28.subOK 27 = true := by decide +kernel

theorem famT28_sub28_ok : famT28.subOK 28 = true := by decide +kernel

theorem famT28_sub29_ok : famT28.subOK 29 = true := by decide +kernel

theorem famT28_sub30_ok : famT28.subOK 30 = true := by decide +kernel

theorem famT28_sub31_ok : famT28.subOK 31 = true := by decide +kernel

theorem famT28_sub32_ok : famT28.subOK 32 = true := by decide +kernel

theorem famT28_sub33_ok : famT28.subOK 33 = true := by decide +kernel

theorem famT28_sub34_ok : famT28.subOK 34 = true := by decide +kernel

theorem famT28_sub35_ok : famT28.subOK 35 = true := by decide +kernel

theorem famT28_recs : ∀ r ∈ famT28.recs, famT28.recOK r = true :=
  famT28.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [famT28_recs_ok0, famT28_recs_ok1, famT28_recs_ok2, famT28_recs_ok3, famT28_recs_ok4, famT28_recs_ok5, famT28_recs_ok6, famT28_recs_ok7, famT28_recs_ok8, famT28_recs_ok9, famT28_recs_ok10, famT28_recs_ok11, famT28_recs_ok12])
    (by decide +kernel)

theorem famT28_subs : ∀ k < famT28.subs.length, famT28.subOK k = true := by
  intro k hk
  have h : famT28.subs.length = 36 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT28_sub0_ok, famT28_sub1_ok, famT28_sub2_ok, famT28_sub3_ok, famT28_sub4_ok, famT28_sub5_ok, famT28_sub6_ok, famT28_sub7_ok, famT28_sub8_ok, famT28_sub9_ok, famT28_sub10_ok, famT28_sub11_ok, famT28_sub12_ok, famT28_sub13_ok, famT28_sub14_ok, famT28_sub15_ok, famT28_sub16_ok, famT28_sub17_ok, famT28_sub18_ok, famT28_sub19_ok, famT28_sub20_ok, famT28_sub21_ok, famT28_sub22_ok, famT28_sub23_ok, famT28_sub24_ok, famT28_sub25_ok, famT28_sub26_ok, famT28_sub27_ok, famT28_sub28_ok, famT28_sub29_ok, famT28_sub30_ok, famT28_sub31_ok, famT28_sub32_ok, famT28_sub33_ok, famT28_sub34_ok, famT28_sub35_ok]

end Kalai5.A16
