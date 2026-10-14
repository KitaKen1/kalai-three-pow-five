import Kalai5.A16.Data20.Fam34
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 34 at twenty facets. -/

namespace Kalai5.A16

theorem famT34_check : famT34.check21 = true := by decide +kernel

theorem famT34_recs_ok0 : famT34.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT34_recs_ok1 : famT34.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT34_recs_ok2 : famT34.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT34_recs_ok3 : famT34.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT34_recs_ok4 : famT34.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT34_recs_ok5 : famT34.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT34_recs_ok6 : famT34.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT34_recs_ok7 : famT34.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT34_recs_ok8 : famT34.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT34_recs_ok9 : famT34.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT34_recs_ok10 : famT34.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT34_recs_ok11 : famT34.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT34_recs_ok12 : famT34.recsOK (40 * 12) 40 = true := by decide +kernel

theorem famT34_recs_ok13 : famT34.recsOK (40 * 13) 40 = true := by decide +kernel

theorem famT34_recs_ok14 : famT34.recsOK (40 * 14) 40 = true := by decide +kernel

theorem famT34_recs_ok15 : famT34.recsOK (40 * 15) 40 = true := by decide +kernel

theorem famT34_sub0_ok : famT34.subOK 0 = true := by decide +kernel

theorem famT34_sub1_ok : famT34.subOK 1 = true := by decide +kernel

theorem famT34_sub2_ok : famT34.subOK 2 = true := by decide +kernel

theorem famT34_sub3_ok : famT34.subOK 3 = true := by decide +kernel

theorem famT34_sub4_ok : famT34.subOK 4 = true := by decide +kernel

theorem famT34_sub5_ok : famT34.subOK 5 = true := by decide +kernel

theorem famT34_sub6_ok : famT34.subOK 6 = true := by decide +kernel

theorem famT34_sub7_ok : famT34.subOK 7 = true := by decide +kernel

theorem famT34_sub8_ok : famT34.subOK 8 = true := by decide +kernel

theorem famT34_sub9_ok : famT34.subOK 9 = true := by decide +kernel

theorem famT34_sub10_ok : famT34.subOK 10 = true := by decide +kernel

theorem famT34_sub11_ok : famT34.subOK 11 = true := by decide +kernel

theorem famT34_sub12_ok : famT34.subOK 12 = true := by decide +kernel

theorem famT34_sub13_ok : famT34.subOK 13 = true := by decide +kernel

theorem famT34_sub14_ok : famT34.subOK 14 = true := by decide +kernel

theorem famT34_sub15_ok : famT34.subOK 15 = true := by decide +kernel

theorem famT34_sub16_ok : famT34.subOK 16 = true := by decide +kernel

theorem famT34_sub17_ok : famT34.subOK 17 = true := by decide +kernel

theorem famT34_sub18_ok : famT34.subOK 18 = true := by decide +kernel

theorem famT34_sub19_ok : famT34.subOK 19 = true := by decide +kernel

theorem famT34_sub20_ok : famT34.subOK 20 = true := by decide +kernel

theorem famT34_sub21_ok : famT34.subOK 21 = true := by decide +kernel

theorem famT34_sub22_ok : famT34.subOK 22 = true := by decide +kernel

theorem famT34_sub23_ok : famT34.subOK 23 = true := by decide +kernel

theorem famT34_sub24_ok : famT34.subOK 24 = true := by decide +kernel

theorem famT34_sub25_ok : famT34.subOK 25 = true := by decide +kernel

theorem famT34_sub26_ok : famT34.subOK 26 = true := by decide +kernel

theorem famT34_sub27_ok : famT34.subOK 27 = true := by decide +kernel

theorem famT34_sub28_ok : famT34.subOK 28 = true := by decide +kernel

theorem famT34_sub29_ok : famT34.subOK 29 = true := by decide +kernel

theorem famT34_sub30_ok : famT34.subOK 30 = true := by decide +kernel

theorem famT34_sub31_ok : famT34.subOK 31 = true := by decide +kernel

theorem famT34_sub32_ok : famT34.subOK 32 = true := by decide +kernel

theorem famT34_sub33_ok : famT34.subOK 33 = true := by decide +kernel

theorem famT34_sub34_ok : famT34.subOK 34 = true := by decide +kernel

theorem famT34_sub35_ok : famT34.subOK 35 = true := by decide +kernel

theorem famT34_sub36_ok : famT34.subOK 36 = true := by decide +kernel

theorem famT34_sub37_ok : famT34.subOK 37 = true := by decide +kernel

theorem famT34_sub38_ok : famT34.subOK 38 = true := by decide +kernel

theorem famT34_sub39_ok : famT34.subOK 39 = true := by decide +kernel

theorem famT34_recs : ∀ r ∈ famT34.recs, famT34.recOK r = true :=
  famT34.recs_of_chunks 16 (fun c hc => by
    interval_cases c
    exacts [famT34_recs_ok0, famT34_recs_ok1, famT34_recs_ok2, famT34_recs_ok3, famT34_recs_ok4, famT34_recs_ok5, famT34_recs_ok6, famT34_recs_ok7, famT34_recs_ok8, famT34_recs_ok9, famT34_recs_ok10, famT34_recs_ok11, famT34_recs_ok12, famT34_recs_ok13, famT34_recs_ok14, famT34_recs_ok15])
    (by decide +kernel)

theorem famT34_subs : ∀ k < famT34.subs.length, famT34.subOK k = true := by
  intro k hk
  have h : famT34.subs.length = 40 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT34_sub0_ok, famT34_sub1_ok, famT34_sub2_ok, famT34_sub3_ok, famT34_sub4_ok, famT34_sub5_ok, famT34_sub6_ok, famT34_sub7_ok, famT34_sub8_ok, famT34_sub9_ok, famT34_sub10_ok, famT34_sub11_ok, famT34_sub12_ok, famT34_sub13_ok, famT34_sub14_ok, famT34_sub15_ok, famT34_sub16_ok, famT34_sub17_ok, famT34_sub18_ok, famT34_sub19_ok, famT34_sub20_ok, famT34_sub21_ok, famT34_sub22_ok, famT34_sub23_ok, famT34_sub24_ok, famT34_sub25_ok, famT34_sub26_ok, famT34_sub27_ok, famT34_sub28_ok, famT34_sub29_ok, famT34_sub30_ok, famT34_sub31_ok, famT34_sub32_ok, famT34_sub33_ok, famT34_sub34_ok, famT34_sub35_ok, famT34_sub36_ok, famT34_sub37_ok, famT34_sub38_ok, famT34_sub39_ok]

end Kalai5.A16
