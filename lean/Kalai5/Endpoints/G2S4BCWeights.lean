import Kalai5.Endpoints.G2S4BCPrisms

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.g2s4_bc_c_7127_zero
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hC : faceRow P F = G2S4.cRow) :
    tcnt P F (7,12,7) = 0 := by
  have hu := hP.g2s4_bc_c_upper hp hb hF h4 hC
  by_contra hz
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (7,12,7))
  have ht' := ht
  simp only [tri3,Prod.mk.injEq] at ht'
  have hl := hP.three_ridge_exc_le_weight hT hTF hT3 (by omega) (hP.g2s4_bc_no_big hp F)
  have he := hP.exc_threeface hT hT3
  rw [ht'.2.1,ht'.2.2] at he
  omega

theorem IsCSPolytope5.g2s4_bc_b_6106_positive
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hB : faceRow P F = G2S4.bRow) :
    1 ≤ tcnt P F (6,10,6) := by
  have hother : ∀ H ∈ faces P, dim H = 4 → faceRow P H ≠ G2S4.bRow → tcnt P H (7,12,7) = 0 := by
    intro H hH hH4 hne
    rcases hP.g2s4_bc_row_cases hp hH hH4 with hY | hD | hBr | hC
    · exact hP.small_facet_seven_ridge_zero hH hH4 (by have := congrArg Row.n hY; change cnt P H 0 = 7 at this; omega) 12 7
    · exact hP.small_facet_seven_ridge_zero hH hH4 (by have := congrArg Row.n hD; change cnt P H 0 = 7 at this; omega) 12 7
    · exact (hne hBr).elim
    · exact hP.g2s4_bc_c_7127_zero hp hb hH hH4 hC
  have hz := hP.tcnt_zero_of_unique_pair_row hp (by decide +kernel) (7,12,7) hother hF h4
  have he := hP.b_no_prism_special_ridge hF h4 hB (hP.g2s4_bc_b_prism_zero hp hb hF h4 hB)
  omega

theorem IsCSPolytope5.g2s4_bc_6106_carrier
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (ht : 1 ≤ tcnt P F (6,10,6)) :
    faceRow P F = G2S4.bRow ∨ faceRow P F = G2S4.cRow := by
  rcases hP.g2s4_bc_row_cases hp hF h4 with hY | hD | hB | hC
  · have hz := (hP.small_special_free_counts hF h4 (by rw [hY]; decide +kernel)).1
    omega
  · have hz := (hP.small_special_free_counts hF h4 (by rw [hD]; decide +kernel)).1
    omega
  · exact Or.inl hB
  · exact Or.inr hC

theorem IsCSPolytope5.g2s4_bc_c_6106_positive
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hC : faceRow P F = G2S4.cRow) :
    1 ≤ tcnt P F (6,10,6) := by
  have hm : G2S4.bRow ∈ facetRows P := hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel))
  obtain ⟨B,hB,hB4,hBR⟩ := hP.mem_facetRows hm
  obtain ⟨T,hT,hTB,hT3,ht⟩ := hP.exists_of_tcnt (hP.g2s4_bc_b_6106_positive hp hb hB hB4 hBR)
  obtain ⟨H,hH,hH4,hHB,hTH⟩ := hP.exists_other_facet hT hT3 hTB
  have hne := hP.unique_pair_ridge_partner_row_ne hp (by decide +kernel)
    hB hB4 hBR hH hH4 hHB hT hTB hTH
  have hpos := hP.one_le_tcnt hT hTH hT3
  rw [ht] at hpos
  have hHR := (hP.g2s4_bc_6106_carrier hp hH hH4 hpos).resolve_left hne
  have htwo : ((facetRows P).map fun R => if R = G2S4.cRow then 1 else 0).sum = 2 := by
    rw [(hp.map _).sum_eq]
    decide +kernel
  rcases hP.two_row_facets_eq_or_neg htwo hH hH4 hHR hF h4 hC with he | he
  · rwa [he]
  · rw [he,hP.tcnt_neg]
    exact hpos

theorem IsCSPolytope5.g2s4_bc_c_weight_six_lower
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hC : faceRow P F = G2S4.cRow) :
    6 ≤ q55w P F + 2 * exc P F := by
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (hP.g2s4_bc_c_6106_positive hp hb hF h4 hC)
  simp only [tri3,Prod.mk.injEq] at ht
  have hl := hP.three_ridge_exc_le_weight hT hTF hT3 (by omega) (hP.g2s4_bc_no_big hp F)
  have he := hP.exc_threeface hT hT3
  rw [ht.2.1,ht.2.2] at he
  omega

theorem IsCSPolytope5.g2s4_bc_weight_lower
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (G2S4.bcWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold G2S4.bcWeight
  split_ifs with hC
  · exact hP.g2s4_bc_c_weight_six_lower hp hb hF h4 hC
  · exact hP.q55_qFour_row_weight hF h4

theorem IsCSPolytope5.g2s4_bc_weight_eq
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F = G2S4.bcWeight (faceRow P F) := by
  have hl := hP.g2s4_bc_weight_lower hp hb hF h4
  have hu := hP.twice_facet_weight_le_of_lower_bound G2S4.bcWeight
    (fun _ => hP.g2s4_bc_weight_lower hp hb) 132 hb hF h4
  have hs : ((facetRows P).map G2S4.bcWeight).sum = 132 := by
    rw [(hp.map _).sum_eq]
    decide +kernel
  rw [hs] at hu
  omega

end Kalai5

