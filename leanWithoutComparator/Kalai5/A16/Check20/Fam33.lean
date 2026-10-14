import Kalai5.A16.Data20.Fam33
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 33 at twenty facets. -/

namespace Kalai5.A16

theorem famT33_check : famT33.check21 = true := by decide +kernel

theorem famT33_recs_ok0 : famT33.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT33_recs_ok1 : famT33.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT33_recs_ok2 : famT33.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT33_recs_ok3 : famT33.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT33_recs_ok4 : famT33.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT33_recs_ok5 : famT33.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT33_recs_ok6 : famT33.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT33_recs_ok7 : famT33.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT33_recs_ok8 : famT33.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT33_recs_ok9 : famT33.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT33_recs_ok10 : famT33.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT33_recs_ok11 : famT33.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT33_recs_ok12 : famT33.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT33_recs_ok13 : famT33.recsOK (40 * 13) 40 = true := by decide +kernel

theorem famT33_sub0_ok : famT33.subOK 0 = true := by decide +kernel

theorem famT33_sub1_ok : famT33.subOK 1 = true := by decide +kernel

theorem famT33_sub2_ok : famT33.subOK 2 = true := by decide +kernel

theorem famT33_sub3_ok : famT33.subOK 3 = true := by decide +kernel

theorem famT33_sub4_ok : famT33.subOK 4 = true := by decide +kernel

theorem famT33_sub5_ok : famT33.subOK 5 = true := by decide +kernel

theorem famT33_sub6_ok : famT33.subOK 6 = true := by decide +kernel

theorem famT33_sub7_ok : famT33.subOK 7 = true := by decide +kernel

theorem famT33_sub8_ok : famT33.subOK 8 = true := by decide +kernel

theorem famT33_sub9_ok : famT33.subOK 9 = true := by decide +kernel

theorem famT33_sub10_ok : famT33.subOK 10 = true := by decide +kernel

theorem famT33_sub11_ok : famT33.subOK 11 = true := by decide +kernel

theorem famT33_sub12_ok : famT33.subOK 12 = true := by decide +kernel

theorem famT33_sub13_ok : famT33.subOK 13 = true := by decide +kernel

theorem famT33_sub14_ok : famT33.subOK 14 = true := by decide +kernel

theorem famT33_sub15_ok : famT33.subOK 15 = true := by decide +kernel

theorem famT33_sub16_ok : famT33.subOK 16 = true := by decide +kernel

theorem famT33_sub17_ok : famT33.subOK 17 = true := by decide +kernel

theorem famT33_sub18_ok : famT33.subOK 18 = true := by decide +kernel

theorem famT33_sub19_ok : famT33.subOK 19 = true := by decide +kernel

theorem famT33_sub20_ok : famT33.subOK 20 = true := by decide +kernel

theorem famT33_sub21_ok : famT33.subOK 21 = true := by decide +kernel

theorem famT33_sub22_ok : famT33.subOK 22 = true := by decide +kernel

theorem famT33_sub23_ok : famT33.subOK 23 = true := by decide +kernel

theorem famT33_sub24_ok : famT33.subOK 24 = true := by decide +kernel

theorem famT33_sub25_ok : famT33.subOK 25 = true := by decide +kernel

theorem famT33_sub26_ok : famT33.subOK 26 = true := by decide +kernel

theorem famT33_sub27_ok : famT33.subOK 27 = true := by decide +kernel

theorem famT33_sub28_ok : famT33.subOK 28 = true := by decide +kernel

theorem famT33_sub29_ok : famT33.subOK 29 = true := by decide +kernel

theorem famT33_sub30_ok : famT33.subOK 30 = true := by decide +kernel

theorem famT33_sub31_ok : famT33.subOK 31 = true := by decide +kernel

theorem famT33_sub32_ok : famT33.subOK 32 = true := by decide +kernel

theorem famT33_sub33_ok : famT33.subOK 33 = true := by decide +kernel

theorem famT33_sub34_ok : famT33.subOK 34 = true := by decide +kernel

theorem famT33_sub35_ok : famT33.subOK 35 = true := by decide +kernel

theorem famT33_sub36_ok : famT33.subOK 36 = true := by decide +kernel

theorem famT33_recs : ∀ r ∈ famT33.recs, famT33.recOK r = true :=
  famT33.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [famT33_recs_ok0, famT33_recs_ok1, famT33_recs_ok2, famT33_recs_ok3, famT33_recs_ok4, famT33_recs_ok5, famT33_recs_ok6, famT33_recs_ok7, famT33_recs_ok8, famT33_recs_ok9, famT33_recs_ok10, famT33_recs_ok11, famT33_recs_ok12, famT33_recs_ok13])
    (by decide +kernel)

theorem famT33_subs : ∀ k < famT33.subs.length, famT33.subOK k = true := by
  intro k hk
  have h : famT33.subs.length = 37 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT33_sub0_ok, famT33_sub1_ok, famT33_sub2_ok, famT33_sub3_ok, famT33_sub4_ok, famT33_sub5_ok, famT33_sub6_ok, famT33_sub7_ok, famT33_sub8_ok, famT33_sub9_ok, famT33_sub10_ok, famT33_sub11_ok, famT33_sub12_ok, famT33_sub13_ok, famT33_sub14_ok, famT33_sub15_ok, famT33_sub16_ok, famT33_sub17_ok, famT33_sub18_ok, famT33_sub19_ok, famT33_sub20_ok, famT33_sub21_ok, famT33_sub22_ok, famT33_sub23_ok, famT33_sub24_ok, famT33_sub25_ok, famT33_sub26_ok, famT33_sub27_ok, famT33_sub28_ok, famT33_sub29_ok, famT33_sub30_ok, famT33_sub31_ok, famT33_sub32_ok, famT33_sub33_ok, famT33_sub34_ok, famT33_sub35_ok, famT33_sub36_ok]

end Kalai5.A16
