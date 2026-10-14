import Kalai5.Endpoints.FullNineTetra
import Kalai5.Endpoints.FullPolygonRowBudget

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Two full pairs and a nine-ridge full facet rule out large polygons
throughout the polytope. -/
theorem IsCSPolytope5.full_nine_big2_zero
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    {F H : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hF8 : cnt P F 0 = 8) (hr : cnt P F 3 = 9)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F) (X : Set E5) : big2 P X = 0 := by
  have bound : ∀ {K : Set E5}, K ∈ faces P → dim K = 4 → cnt P K 0 = 8 →
      K ≠ F → K ≠ -F → cnt P (F ∩ K) 0 ≤ 4 := by
    intro K hK hK4 hK8 hKF hKnF
    obtain ⟨T,hT,hTF,hT3,hTK⟩ := hP.full_nine_meets_other_full hv hh hc hF hF4 hF8 hr hK hK4 hK8 hKF hKnF
    have he := hP.three_face_eq_inter hF hF4 hK hK4 hKF.symm hT hT3 hTF hTK
    rw [← he]
    by_contra hn
    exact hP.full_nine_large_ridge_partner_nonfull hv hh hc hF hF4 hF8 hr
      hT hTF hT3 (by omega) hK hK4 hKF hTK hK8
  have hplus := bound hH hH4 hH8 hHF hHnF
  have hminus := bound (neg_mem_faces hP.symm hH) (by rw [dim_neg,hH4])
    (by rw [hP.cnt_neg,hH8])
    (by intro he; apply hHnF; rw [← he,neg_neg]) (fun he => hHF (neg_injective he))
  have hz : big2 P F = 0 := by
    by_contra hn
    obtain ⟨Q,hQ,hQF,hQ2,hQ5⟩ := Set.nonempty_of_ncard_ne_zero hn
    have hHP : H ≠ P := hP.ne_of_dim_ne' (by rw [hH4]; decide)
    rcases hP.large_polygon_sub_full_or_neg hH hHP (by omega) hQ hQ2 hQ5 with hs | hs
    · have hb := Set.ncard_le_ncard (vset_mono' (subset_inter hQF hs)) (hP.vset_finite (F ∩ H))
      rw [← cnt_eq_vset,← cnt_eq_vset] at hb
      omega
    · have hb := Set.ncard_le_ncard (vset_mono' (subset_inter hQF hs)) (hP.vset_finite (F ∩ -H))
      rw [← cnt_eq_vset,← cnt_eq_vset] at hb
      omega
  exact hP.big2_zero_of_full_facet hF hF4 (by omega) hz X

/-- Distinct six-vertex ridges in a seven-vertex facet force a polygon
with at least five vertices. -/
theorem IsCSPolytope5.six_vertex_ridge_unique_of_seven_no_big {F T U : Set E5}
    (hF7 : cnt P F 0 = 7) (hz : big2 P F = 0)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (hT6 : cnt P T 0 = 6)
    (hU : U ∈ faces P) (hUF : U ⊆ F) (hU3 : dim U = 3) (hU6 : cnt P U 0 = 6) : T = U := by
  by_contra hne
  obtain ⟨hs,hu⟩ := hP.cnt_add_le hTF hUF (rfl : T ∩ U = T ∩ U)
  have hcap := Set.ncard_le_ncard hu (hP.vset_finite F)
  rw [← cnt_eq_vset] at hcap
  have hi5 : 5 ≤ cnt P (T ∩ U) 0 := by omega
  have hIne : (T ∩ U).Nonempty := by
    obtain ⟨v,hv⟩ := Set.nonempty_of_ncard_ne_zero
      (show (vset P (T ∩ U)).ncard ≠ 0 by rw [← cnt_eq_vset]; omega)
    exact hv.1.1.mono hv.2.1
  have hI := inter_mem_faces_of_nonempty hT hU hIne
  have hIT := mem_faces_of_subset (face_subset hT) hI inter_subset_left
  have hnT : T ∩ U ≠ T := by
    intro he
    exact hne (hP.eq_of_subset_of_dim_le hT hU
      (by rw [← he]; exact inter_subset_right) (by omega))
  have hd := dim_lt_of_mem_faces_ne hIT hnT
  have hI2 : dim (T ∩ U) = 2 := by
    by_contra hn
    have hb := hP.cnt_le_two_of_dim_le_one hI (by omega)
    omega
  have hfin : {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ 5 ≤ cnt P Q 0}.Finite :=
    hP.faces_finite.subset fun Q hQ => hQ.1
  have hpos : 0 < big2 P F := (Set.ncard_pos hfin).2
    ⟨T ∩ U,hI,inter_subset_left.trans hTF,hI2,hi5⟩
  omega

theorem IsCSPolytope5.seven_no_big_6106_le_one {F : Set E5}
    (hF7 : cnt P F 0 = 7) (hz : big2 P F = 0) : tcnt P F (6,10,6) ≤ 1 := by
  by_contra hn
  obtain ⟨T,U,hne,hT,hU⟩ := hP.exists_two_of_tcnt (by omega : 2 ≤ tcnt P F (6,10,6))
  exact hne (hP.six_vertex_ridge_unique_of_seven_no_big hF7 hz
    hT.1 hT.2.1 hT.2.2.1 (congrArg Prod.fst hT.2.2.2)
    hU.1 hU.2.1 hU.2.2.1 (congrArg Prod.fst hU.2.2.2))

end Kalai5
