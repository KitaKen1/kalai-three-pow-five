import Kalai5.A16.Data20.Fam41
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 41 at twenty facets. -/

namespace Kalai5.A16

theorem famT41_check : famT41.check21 = true := by decide +kernel

theorem famT41_recs_ok0 : famT41.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT41_recs_ok1 : famT41.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT41_recs_ok2 : famT41.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT41_recs_ok3 : famT41.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT41_recs_ok4 : famT41.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT41_recs_ok5 : famT41.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT41_recs_ok6 : famT41.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT41_recs_ok7 : famT41.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT41_recs_ok8 : famT41.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT41_recs_ok9 : famT41.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT41_recs_ok10 : famT41.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT41_recs_ok11 : famT41.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT41_sub0_ok : famT41.subOK 0 = true := by decide +kernel

theorem famT41_sub1_ok : famT41.subOK 1 = true := by decide +kernel

theorem famT41_sub2_ok : famT41.subOK 2 = true := by decide +kernel

theorem famT41_sub3_ok : famT41.subOK 3 = true := by decide +kernel

theorem famT41_sub4_ok : famT41.subOK 4 = true := by decide +kernel

theorem famT41_sub5_ok : famT41.subOK 5 = true := by decide +kernel

theorem famT41_sub6_ok : famT41.subOK 6 = true := by decide +kernel

theorem famT41_sub7_ok : famT41.subOK 7 = true := by decide +kernel

theorem famT41_sub8_ok : famT41.subOK 8 = true := by decide +kernel

theorem famT41_sub9_ok : famT41.subOK 9 = true := by decide +kernel

theorem famT41_sub10_ok : famT41.subOK 10 = true := by decide +kernel

theorem famT41_sub11_ok : famT41.subOK 11 = true := by decide +kernel

theorem famT41_sub12_ok : famT41.subOK 12 = true := by decide +kernel

theorem famT41_sub13_ok : famT41.subOK 13 = true := by decide +kernel

theorem famT41_sub14_ok : famT41.subOK 14 = true := by decide +kernel

theorem famT41_sub15_ok : famT41.subOK 15 = true := by decide +kernel

theorem famT41_sub16_ok : famT41.subOK 16 = true := by decide +kernel

theorem famT41_sub17_ok : famT41.subOK 17 = true := by decide +kernel

theorem famT41_sub18_ok : famT41.subOK 18 = true := by decide +kernel

theorem famT41_sub19_ok : famT41.subOK 19 = true := by decide +kernel

theorem famT41_sub20_ok : famT41.subOK 20 = true := by decide +kernel

theorem famT41_sub21_ok : famT41.subOK 21 = true := by decide +kernel

theorem famT41_sub22_ok : famT41.subOK 22 = true := by decide +kernel

theorem famT41_sub23_ok : famT41.subOK 23 = true := by decide +kernel

theorem famT41_sub24_ok : famT41.subOK 24 = true := by decide +kernel

theorem famT41_sub25_ok : famT41.subOK 25 = true := by decide +kernel

theorem famT41_sub26_ok : famT41.subOK 26 = true := by decide +kernel

theorem famT41_sub27_ok : famT41.subOK 27 = true := by decide +kernel

theorem famT41_sub28_ok : famT41.subOK 28 = true := by decide +kernel

theorem famT41_sub29_ok : famT41.subOK 29 = true := by decide +kernel

theorem famT41_sub30_ok : famT41.subOK 30 = true := by decide +kernel

theorem famT41_sub31_ok : famT41.subOK 31 = true := by decide +kernel

theorem famT41_sub32_ok : famT41.subOK 32 = true := by decide +kernel

theorem famT41_sub33_ok : famT41.subOK 33 = true := by decide +kernel

theorem famT41_sub34_ok : famT41.subOK 34 = true := by decide +kernel

theorem famT41_sub35_ok : famT41.subOK 35 = true := by decide +kernel

theorem famT41_sub36_ok : famT41.subOK 36 = true := by decide +kernel

theorem famT41_sub37_ok : famT41.subOK 37 = true := by decide +kernel

theorem famT41_sub38_ok : famT41.subOK 38 = true := by decide +kernel

theorem famT41_sub39_ok : famT41.subOK 39 = true := by decide +kernel

theorem famT41_recs : ∀ r ∈ famT41.recs, famT41.recOK r = true :=
  famT41.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [famT41_recs_ok0, famT41_recs_ok1, famT41_recs_ok2, famT41_recs_ok3, famT41_recs_ok4, famT41_recs_ok5, famT41_recs_ok6, famT41_recs_ok7, famT41_recs_ok8, famT41_recs_ok9, famT41_recs_ok10, famT41_recs_ok11])
    (by decide +kernel)

theorem famT41_subs : ∀ k < famT41.subs.length, famT41.subOK k = true := by
  intro k hk
  have h : famT41.subs.length = 40 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT41_sub0_ok, famT41_sub1_ok, famT41_sub2_ok, famT41_sub3_ok, famT41_sub4_ok, famT41_sub5_ok, famT41_sub6_ok, famT41_sub7_ok, famT41_sub8_ok, famT41_sub9_ok, famT41_sub10_ok, famT41_sub11_ok, famT41_sub12_ok, famT41_sub13_ok, famT41_sub14_ok, famT41_sub15_ok, famT41_sub16_ok, famT41_sub17_ok, famT41_sub18_ok, famT41_sub19_ok, famT41_sub20_ok, famT41_sub21_ok, famT41_sub22_ok, famT41_sub23_ok, famT41_sub24_ok, famT41_sub25_ok, famT41_sub26_ok, famT41_sub27_ok, famT41_sub28_ok, famT41_sub29_ok, famT41_sub30_ok, famT41_sub31_ok, famT41_sub32_ok, famT41_sub33_ok, famT41_sub34_ok, famT41_sub35_ok, famT41_sub36_ok, famT41_sub37_ok, famT41_sub38_ok, famT41_sub39_ok]

end Kalai5.A16
