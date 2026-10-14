import Kalai5.A16.Data20.Fam44
import Kalai5.A16.Walk

/-! Kernel checks of A16 family 44 at twenty facets. -/

namespace Kalai5.A16

theorem famT44_check : famT44.check21 = true := by decide +kernel

theorem famT44_recs_ok0 : famT44.recsOK (40 * 0) 40 = true := by decide +kernel

theorem famT44_recs_ok1 : famT44.recsOK (40 * 1) 40 = true := by decide +kernel

theorem famT44_recs_ok2 : famT44.recsOK (40 * 2) 40 = true := by decide +kernel

theorem famT44_recs_ok3 : famT44.recsOK (40 * 3) 40 = true := by decide +kernel

theorem famT44_recs_ok4 : famT44.recsOK (40 * 4) 40 = true := by decide +kernel

theorem famT44_recs_ok5 : famT44.recsOK (40 * 5) 40 = true := by decide +kernel

theorem famT44_recs_ok6 : famT44.recsOK (40 * 6) 40 = true := by decide +kernel

theorem famT44_recs_ok7 : famT44.recsOK (40 * 7) 40 = true := by decide +kernel

theorem famT44_recs_ok8 : famT44.recsOK (40 * 8) 40 = true := by decide +kernel

theorem famT44_recs_ok9 : famT44.recsOK (40 * 9) 40 = true := by decide +kernel

theorem famT44_recs_ok10 : famT44.recsOK (40 * 10) 40 = true := by decide +kernel

theorem famT44_recs_ok11 : famT44.recsOK (40 * 11) 40 = true := by decide +kernel

theorem famT44_sub0_ok : famT44.subOK 0 = true := by decide +kernel

theorem famT44_sub1_ok : famT44.subOK 1 = true := by decide +kernel

theorem famT44_sub2_ok : famT44.subOK 2 = true := by decide +kernel

theorem famT44_sub3_ok : famT44.subOK 3 = true := by decide +kernel

theorem famT44_sub4_ok : famT44.subOK 4 = true := by decide +kernel

theorem famT44_sub5_ok : famT44.subOK 5 = true := by decide +kernel

theorem famT44_sub6_ok : famT44.subOK 6 = true := by decide +kernel

theorem famT44_sub7_ok : famT44.subOK 7 = true := by decide +kernel

theorem famT44_sub8_ok : famT44.subOK 8 = true := by decide +kernel

theorem famT44_sub9_ok : famT44.subOK 9 = true := by decide +kernel

theorem famT44_sub10_ok : famT44.subOK 10 = true := by decide +kernel

theorem famT44_sub11_ok : famT44.subOK 11 = true := by decide +kernel

theorem famT44_sub12_ok : famT44.subOK 12 = true := by decide +kernel

theorem famT44_sub13_ok : famT44.subOK 13 = true := by decide +kernel

theorem famT44_sub14_ok : famT44.subOK 14 = true := by decide +kernel

theorem famT44_sub15_ok : famT44.subOK 15 = true := by decide +kernel

theorem famT44_sub16_ok : famT44.subOK 16 = true := by decide +kernel

theorem famT44_sub17_ok : famT44.subOK 17 = true := by decide +kernel

theorem famT44_sub18_ok : famT44.subOK 18 = true := by decide +kernel

theorem famT44_sub19_ok : famT44.subOK 19 = true := by decide +kernel

theorem famT44_sub20_ok : famT44.subOK 20 = true := by decide +kernel

theorem famT44_sub21_ok : famT44.subOK 21 = true := by decide +kernel

theorem famT44_sub22_ok : famT44.subOK 22 = true := by decide +kernel

theorem famT44_sub23_ok : famT44.subOK 23 = true := by decide +kernel

theorem famT44_sub24_ok : famT44.subOK 24 = true := by decide +kernel

theorem famT44_sub25_ok : famT44.subOK 25 = true := by decide +kernel

theorem famT44_sub26_ok : famT44.subOK 26 = true := by decide +kernel

theorem famT44_sub27_ok : famT44.subOK 27 = true := by decide +kernel

theorem famT44_sub28_ok : famT44.subOK 28 = true := by decide +kernel

theorem famT44_sub29_ok : famT44.subOK 29 = true := by decide +kernel

theorem famT44_sub30_ok : famT44.subOK 30 = true := by decide +kernel

theorem famT44_sub31_ok : famT44.subOK 31 = true := by decide +kernel

theorem famT44_sub32_ok : famT44.subOK 32 = true := by decide +kernel

theorem famT44_sub33_ok : famT44.subOK 33 = true := by decide +kernel

theorem famT44_sub34_ok : famT44.subOK 34 = true := by decide +kernel

theorem famT44_sub35_ok : famT44.subOK 35 = true := by decide +kernel

theorem famT44_sub36_ok : famT44.subOK 36 = true := by decide +kernel

theorem famT44_sub37_ok : famT44.subOK 37 = true := by decide +kernel

theorem famT44_sub38_ok : famT44.subOK 38 = true := by decide +kernel

theorem famT44_recs : ∀ r ∈ famT44.recs, famT44.recOK r = true :=
  famT44.recs_of_chunks 12 (fun c hc => by
    interval_cases c
    exacts [famT44_recs_ok0, famT44_recs_ok1, famT44_recs_ok2, famT44_recs_ok3, famT44_recs_ok4, famT44_recs_ok5, famT44_recs_ok6, famT44_recs_ok7, famT44_recs_ok8, famT44_recs_ok9, famT44_recs_ok10, famT44_recs_ok11])
    (by decide +kernel)

theorem famT44_subs : ∀ k < famT44.subs.length, famT44.subOK k = true := by
  intro k hk
  have h : famT44.subs.length = 39 := by decide +kernel
  rw [h] at hk
  interval_cases k
  exacts [famT44_sub0_ok, famT44_sub1_ok, famT44_sub2_ok, famT44_sub3_ok, famT44_sub4_ok, famT44_sub5_ok, famT44_sub6_ok, famT44_sub7_ok, famT44_sub8_ok, famT44_sub9_ok, famT44_sub10_ok, famT44_sub11_ok, famT44_sub12_ok, famT44_sub13_ok, famT44_sub14_ok, famT44_sub15_ok, famT44_sub16_ok, famT44_sub17_ok, famT44_sub18_ok, famT44_sub19_ok, famT44_sub20_ok, famT44_sub21_ok, famT44_sub22_ok, famT44_sub23_ok, famT44_sub24_ok, famT44_sub25_ok, famT44_sub26_ok, famT44_sub27_ok, famT44_sub28_ok, famT44_sub29_ok, famT44_sub30_ok, famT44_sub31_ok, famT44_sub32_ok, famT44_sub33_ok, famT44_sub34_ok, famT44_sub35_ok, famT44_sub36_ok, famT44_sub37_ok, famT44_sub38_ok]

end Kalai5.A16
