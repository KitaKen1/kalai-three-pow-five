import Kalai5.A16.Data20.Fam26
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 26 at twenty facets. -/

namespace Kalai5.A16

theorem famT26_check : famT26.check21 = true := by decide +kernel

theorem famT26_recs_ok0 : famT26.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT26_recs_ok1 : famT26.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT26_recs_ok2 : famT26.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT26_recs_ok3 : famT26.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT26_recs_ok4 : famT26.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT26_recs_ok5 : famT26.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT26_recs_ok6 : famT26.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT26_recs_ok7 : famT26.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT26_recs_ok8 : famT26.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT26_recs_ok9 : famT26.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT26_recs_ok10 : famT26.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT26_recs_ok11 : famT26.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT26_recs_ok12 : famT26.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT26_sub0_ok : famT26.subOK 0 = true := by decide +kernel

theorem famT26_sub1_ok : famT26.subOK 1 = true := by decide +kernel

theorem famT26_sub2_ok : famT26.subOK 2 = true := by decide +kernel

theorem famT26_sub3_ok : famT26.subOK 3 = true := by decide +kernel

theorem famT26_sub4_ok : famT26.subOK 4 = true := by decide +kernel

theorem famT26_sub5_ok : famT26.subOK 5 = true := by decide +kernel

theorem famT26_sub6_ok : famT26.subOK 6 = true := by decide +kernel

theorem famT26_sub7_ok : famT26.subOK 7 = true := by decide +kernel

theorem famT26_sub8_ok : famT26.subOK 8 = true := by decide +kernel

theorem famT26_sub9_ok : famT26.subOK 9 = true := by decide +kernel

theorem famT26_sub10_ok : famT26.subOK 10 = true := by decide +kernel

theorem famT26_sub11_ok : famT26.subOK 11 = true := by decide +kernel

theorem famT26_sub12_ok : famT26.subOK 12 = true := by decide +kernel

theorem famT26_sub13_ok : famT26.subOK 13 = true := by decide +kernel

theorem famT26_sub14_ok : famT26.subOK 14 = true := by decide +kernel

theorem famT26_sub15_ok : famT26.subOK 15 = true := by decide +kernel

theorem famT26_sub16_ok : famT26.subOK 16 = true := by decide +kernel

theorem famT26_sub17_ok : famT26.subOK 17 = true := by decide +kernel

theorem famT26_sub18_ok : famT26.subOK 18 = true := by decide +kernel

theorem famT26_sub19_ok : famT26.subOK 19 = true := by decide +kernel

theorem famT26_sub20_ok : famT26.subOK 20 = true := by decide +kernel

theorem famT26_sub21_ok : famT26.subOK 21 = true := by decide +kernel

theorem famT26_sub22_ok : famT26.subOK 22 = true := by decide +kernel

theorem famT26_sub23_ok : famT26.subOK 23 = true := by decide +kernel

theorem famT26_sub24_ok : famT26.subOK 24 = true := by decide +kernel

theorem famT26_sub25_ok : famT26.subOK 25 = true := by decide +kernel

theorem famT26_sub26_ok : famT26.subOK 26 = true := by decide +kernel

theorem famT26_sub27_ok : famT26.subOK 27 = true := by decide +kernel

theorem famT26_sub28_ok : famT26.subOK 28 = true := by decide +kernel

theorem famT26_sub29_ok : famT26.subOK 29 = true := by decide +kernel

theorem famT26_sub30_ok : famT26.subOK 30 = true := by decide +kernel

theorem famT26_sub31_ok : famT26.subOK 31 = true := by decide +kernel

theorem famT26_sub32_ok : famT26.subOK 32 = true := by decide +kernel

theorem famT26_sub33_ok : famT26.subOK 33 = true := by decide +kernel

theorem famT26_sub34_ok : famT26.subOK 34 = true := by decide +kernel

theorem famT26_sub35_ok : famT26.subOK 35 = true := by decide +kernel

theorem famT26_sub36_ok : famT26.subOK 36 = true := by decide +kernel

theorem famT26_recs : ∀ r ∈ famT26.recs, famT26.recOK r = true :=
  famT26.recs_of_chunks 13 (fun c hc => by
    interval_cases c
    exacts [famT26_recs_ok0, famT26_recs_ok1, famT26_recs_ok2, famT26_recs_ok3, famT26_recs_ok4, famT26_recs_ok5, famT26_recs_ok6, famT26_recs_ok7, famT26_recs_ok8, famT26_recs_ok9, famT26_recs_ok10, famT26_recs_ok11, famT26_recs_ok12])
    (by decide +kernel)

theorem famT26_subs : ∀ k < famT26.subs.length, famT26.subOK k = true := by
  intro k hk
  have h : famT26.subs.length = 37 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT26_sub0_ok, famT26_sub1_ok, famT26_sub2_ok, famT26_sub3_ok, famT26_sub4_ok, famT26_sub5_ok, famT26_sub6_ok, famT26_sub7_ok, famT26_sub8_ok, famT26_sub9_ok, famT26_sub10_ok, famT26_sub11_ok, famT26_sub12_ok, famT26_sub13_ok, famT26_sub14_ok, famT26_sub15_ok, famT26_sub16_ok, famT26_sub17_ok, famT26_sub18_ok, famT26_sub19_ok, famT26_sub20_ok, famT26_sub21_ok, famT26_sub22_ok, famT26_sub23_ok, famT26_sub24_ok, famT26_sub25_ok, famT26_sub26_ok, famT26_sub27_ok, famT26_sub28_ok, famT26_sub29_ok, famT26_sub30_ok, famT26_sub31_ok, famT26_sub32_ok, famT26_sub33_ok, famT26_sub34_ok, famT26_sub35_ok, famT26_sub36_ok]

end Kalai5.A16
