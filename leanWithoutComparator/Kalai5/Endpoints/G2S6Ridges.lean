import Kalai5.Endpoints.G2S6Weights
import Kalai5.Endpoints.Ridge6117Budget

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.g2s6_d_no_6117
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.dRow) : tcnt P F (6,11,7) = 0 := by
  have hw := hP.g2s6_weight_eq hp hb hF h4
  rw [hR] at hw
  have hf : G2S6.rowWeight G2S6.dRow = 0 := by decide +kernel
  rw [hf] at hw
  exact hP.tcnt_zero_of_small_weight (by decide) (by omega) (by norm_num; omega)

/-- The zero weight selects the bipyramid profile of D, excluding its
alternative with a (6,11,7) ridge. -/
theorem IsCSPolytope5.g2s6_d_ridge_profile
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.dRow) :
    fv8.map (tcnt P F) = [5,2,1,0,0,0,0,0,0,0,0,0] := by
  have hn : cnt P F 0 = 7 := congrArg Row.n hR
  have hz := hP.g2s6_d_no_6117 hp hb hF h4 hR
  obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
  have hcheck : ∀ X ∈ smallRowsX, X.1 = G2S6.dRow →
      X.2.1 = [5,2,1,0,0,0,0] ∨ X.2.1 = [6,1,0,0,0,1,0] := by decide +kernel
  have hcases := hcheck _ hm (by change rowOf F = _; rw [he,hR])
  have hmap : (rowXOf F).2.1 = fv7.map (tcnt P F) := by
    simpa only [← hP.tcnt_eq_card] using (hP.facet_profile hF h4 hn.le).2
  have hbase : fv7.map (tcnt P F) = [5,2,1,0,0,0,0] := by
    rw [hmap] at hcases
    rcases hcases with h | h
    · exact h
    · simp only [fv7,List.map_cons,List.map_nil,List.cons.injEq] at h
      omega
  have h7 := hP.small_facet_seven_ridge_zero hF h4 hn.le
  change (fv7 ++ [(7,11,6),(7,12,7),(7,13,8),(7,14,9),(7,15,10)]).map (tcnt P F) = _
  simp only [List.map_append,hbase,List.map_cons,List.map_nil,h7]
  rfl

/-- Only the H and C pairs can carry the shared (6,11,7) type. -/
theorem IsCSPolytope5.g2s6_6117_carrier
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (ht : 1 ≤ tcnt P F (6,11,7)) :
    faceRow P F = G2S6.hRow ∨ faceRow P F = G2S6.cRow := by
  rcases hP.g2s6_row_cases hp hF h4 with hY | hD | hH | hC
  · have hz := hP.small_rows_6117_zero hF h4 (by rw [hY]; decide +kernel)
    omega
  · have hz := hP.g2s6_d_no_6117 hp hb hF h4 hD
    omega
  · exact Or.inl hH
  · exact Or.inr hC

theorem IsCSPolytope5.g2s6_h_6117_le_one
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.hRow) : tcnt P F (6,11,7) ≤ 1 := by
  let carrier : Row → Prop := fun R => R = G2S6.hRow ∨ R = G2S6.cRow
  have hfree : ∀ H ∈ faces P, dim H = 4 → ¬ carrier (faceRow P H) →
      ∀ t ∈ [(6,11,7)], tcnt P H t = 0 := by
    intro H hH hH4 hf t ht
    simp only [List.mem_singleton] at ht
    subst t
    by_contra hz
    exact hf (hP.g2s6_6117_carrier hp hb hH hH4 (by omega))
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hc := hP.ridge_type_pair_capacity carrier [(6,11,7)] (by decide) hp hfree
    hF h4 (Or.inl hR) (by
      intro t ht u hu
      simp only [List.mem_singleton] at ht hu
      subst t
      subst u
      omega)
  have hk : (G2S6.pairs.filter fun R => decide (carrier R)).length = 2 := by decide +kernel
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hk] at hc
  omega

theorem IsCSPolytope5.g2s6_h_ridge_profile
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.hRow) :
    q4 P F = 2 ∧ big2 P F = 0 ∧ (b55set P F).ncard = 1 ∧
    fv8.map (tcnt P F) = [3,3,1,0,0,1,0,0,0,0,0,0] := by
  have hw := hP.g2s6_weight_eq hp hb hF h4
  rw [hR] at hw
  have hf : G2S6.rowWeight G2S6.hRow = 3 := by decide +kernel
  rw [hf] at hw
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hr : cnt P F 3 = 8 := congrArg Row.r hR
  have hfp : cnt P F 2 = 20 := congrArg Row.p hR
  have hj : incid P F 0 3 = 38 := congrArg Row.J hR
  have he : exc P F = 2 := by
    have he := hP.exc_eq_faceRow hF h4
    rw [hR] at he
    norm_num [G2S6.hRow] at he
    exact he
  have hbig := hP.big2_zero_of_weight_lt_four (by omega : q55w P F + 2 * exc P F < 4)
  have hq := hP.exc_eq_q4_of_big F hbig
  have hb55 := hP.q55w_eq_b55 F
  have hbi := hP.g2s6_h_bipyr_le_one hp hb hF h4 hR
  have h611 := hP.g2s6_h_6117_le_one hp hb hF h4 hR
  have h610 : tcnt P F (6,10,6) = 0 :=
    hP.tcnt_zero_of_small_weight (by decide) (by omega) (by norm_num; omega)
  have h612 : tcnt P F (6,12,8) = 0 :=
    hP.tcnt_zero_of_polygon_count hF h4 (by change cnt P F 3 ≤ 8; omega)
  have h7 := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn (by omega)
  have h7a := h7 11 6
  have h7b := h7 12 7
  have h7c := h7 13 8
  have h7d := h7 14 9
  have h7e := h7 15 10
  have hpr := hP.h20_no_prism hF h4 hR
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  refine ⟨by omega,hbig,by omega,?_⟩
  simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq,and_true]
  omega

theorem IsCSPolytope5.g2s6_c_ridge_profile
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.cRow) :
    q4 P F = 3 ∧ big2 P F = 0 ∧ (b55set P F).ncard = 2 ∧
    fv8.map (tcnt P F) = [2,5,0,0,0,1,0,0,0,0,0,0] := by
  have hw := hP.g2s6_weight_eq hp hb hF h4
  rw [hR] at hw
  have hf : G2S6.rowWeight G2S6.cRow = 3 := by decide +kernel
  rw [hf] at hw
  obtain ⟨hq,hbig,hb55,h0,h1,h2,h3,h4t,h5,h6,h7⟩ :=
    hP.c_weight_three_profile hF h4 hR (by omega)
  refine ⟨hq,hbig,hb55,?_⟩
  simp only [fv8,List.map_cons,List.map_nil,h0,h1,h2,h3,h4t,h5,h6,h7]

end Kalai5
