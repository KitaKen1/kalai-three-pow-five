import Kalai5.A16.Data20.Fam31
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 31 at twenty facets. -/

namespace Kalai5.A16

theorem famT31_check : famT31.check21 = true := by decide +kernel

theorem famT31_recs_ok0 : famT31.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT31_recs_ok1 : famT31.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT31_recs_ok2 : famT31.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT31_recs_ok3 : famT31.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT31_recs_ok4 : famT31.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT31_recs_ok5 : famT31.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT31_recs_ok6 : famT31.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT31_recs_ok7 : famT31.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT31_recs_ok8 : famT31.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT31_recs_ok9 : famT31.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT31_recs_ok10 : famT31.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT31_recs_ok11 : famT31.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT31_recs_ok12 : famT31.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT31_recs_ok13 : famT31.recsOK (40 * 13) 40 = true := by decide +kernel

theorem famT31_sub0_ok : famT31.subOK 0 = true := by decide +kernel

theorem famT31_sub1_ok : famT31.subOK 1 = true := by decide +kernel

theorem famT31_sub2_ok : famT31.subOK 2 = true := by decide +kernel

theorem famT31_sub3_ok : famT31.subOK 3 = true := by decide +kernel

theorem famT31_sub4_ok : famT31.subOK 4 = true := by decide +kernel

theorem famT31_sub5_ok : famT31.subOK 5 = true := by decide +kernel

theorem famT31_sub6_ok : famT31.subOK 6 = true := by decide +kernel

theorem famT31_sub7_ok : famT31.subOK 7 = true := by decide +kernel

theorem famT31_sub8_ok : famT31.subOK 8 = true := by decide +kernel

theorem famT31_sub9_ok : famT31.subOK 9 = true := by decide +kernel

theorem famT31_sub10_ok : famT31.subOK 10 = true := by decide +kernel

theorem famT31_sub11_ok : famT31.subOK 11 = true := by decide +kernel

theorem famT31_sub12_ok : famT31.subOK 12 = true := by decide +kernel

theorem famT31_sub13_ok : famT31.subOK 13 = true := by decide +kernel

theorem famT31_sub14_ok : famT31.subOK 14 = true := by decide +kernel

theorem famT31_sub15_ok : famT31.subOK 15 = true := by decide +kernel

theorem famT31_sub16_ok : famT31.subOK 16 = true := by decide +kernel

theorem famT31_sub17_ok : famT31.subOK 17 = true := by decide +kernel

theorem famT31_sub18_ok : famT31.subOK 18 = true := by decide +kernel

theorem famT31_sub19_ok : famT31.subOK 19 = true := by decide +kernel

theorem famT31_sub20_ok : famT31.subOK 20 = true := by decide +kernel

theorem famT31_sub21_ok : famT31.subOK 21 = true := by decide +kernel

theorem famT31_sub22_ok : famT31.subOK 22 = true := by decide +kernel

theorem famT31_sub23_ok : famT31.subOK 23 = true := by decide +kernel

theorem famT31_sub24_ok : famT31.subOK 24 = true := by decide +kernel

theorem famT31_sub25_ok : famT31.subOK 25 = true := by decide +kernel

theorem famT31_sub26_ok : famT31.subOK 26 = true := by decide +kernel

theorem famT31_sub27_ok : famT31.subOK 27 = true := by decide +kernel

theorem famT31_sub28_ok : famT31.subOK 28 = true := by decide +kernel

theorem famT31_sub29_ok : famT31.subOK 29 = true := by decide +kernel

theorem famT31_sub30_ok : famT31.subOK 30 = true := by decide +kernel

theorem famT31_sub31_ok : famT31.subOK 31 = true := by decide +kernel

theorem famT31_sub32_ok : famT31.subOK 32 = true := by decide +kernel

theorem famT31_sub33_ok : famT31.subOK 33 = true := by decide +kernel

theorem famT31_sub34_ok : famT31.subOK 34 = true := by decide +kernel

theorem famT31_sub35_ok : famT31.subOK 35 = true := by decide +kernel

theorem famT31_sub36_ok : famT31.subOK 36 = true := by decide +kernel

theorem famT31_sub37_ok : famT31.subOK 37 = true := by decide +kernel

theorem famT31_sub38_ok : famT31.subOK 38 = true := by decide +kernel

theorem famT31_sub39_ok : famT31.subOK 39 = true := by decide +kernel

theorem famT31_recs : ∀ r ∈ famT31.recs, famT31.recOK r = true :=
  famT31.recs_of_chunks 14 (fun c hc => by
    interval_cases c
    exacts [famT31_recs_ok0, famT31_recs_ok1, famT31_recs_ok2, famT31_recs_ok3, famT31_recs_ok4, famT31_recs_ok5, famT31_recs_ok6, famT31_recs_ok7, famT31_recs_ok8, famT31_recs_ok9, famT31_recs_ok10, famT31_recs_ok11, famT31_recs_ok12, famT31_recs_ok13])
    (by decide +kernel)

theorem famT31_subs : ∀ k < famT31.subs.length, famT31.subOK k = true := by
  intro k hk
  have h : famT31.subs.length = 40 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT31_sub0_ok, famT31_sub1_ok, famT31_sub2_ok, famT31_sub3_ok, famT31_sub4_ok, famT31_sub5_ok, famT31_sub6_ok, famT31_sub7_ok, famT31_sub8_ok, famT31_sub9_ok, famT31_sub10_ok, famT31_sub11_ok, famT31_sub12_ok, famT31_sub13_ok, famT31_sub14_ok, famT31_sub15_ok, famT31_sub16_ok, famT31_sub17_ok, famT31_sub18_ok, famT31_sub19_ok, famT31_sub20_ok, famT31_sub21_ok, famT31_sub22_ok, famT31_sub23_ok, famT31_sub24_ok, famT31_sub25_ok, famT31_sub26_ok, famT31_sub27_ok, famT31_sub28_ok, famT31_sub29_ok, famT31_sub30_ok, famT31_sub31_ok, famT31_sub32_ok, famT31_sub33_ok, famT31_sub34_ok, famT31_sub35_ok, famT31_sub36_ok, famT31_sub37_ok, famT31_sub38_ok, famT31_sub39_ok]

end Kalai5.A16
