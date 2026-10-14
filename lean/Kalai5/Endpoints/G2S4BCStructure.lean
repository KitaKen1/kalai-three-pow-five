import Kalai5.Endpoints.G2S4BCWeights

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.g2s4_bc_6106_le_one
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S4.bRow ∨ faceRow P F = G2S4.cRow) :
    tcnt P F (6,10,6) ≤ 1 := by
  let carrier : Row → Prop := fun R => R = G2S4.bRow ∨ R = G2S4.cRow
  have hfree : ∀ H ∈ faces P, dim H = 4 → ¬ carrier (faceRow P H) →
      ∀ t ∈ [(6,10,6)], tcnt P H t = 0 := by
    intro H hH hH4 hn t ht
    simp only [List.mem_singleton] at ht
    subst t
    by_contra hz
    exact hn (hP.g2s4_bc_6106_carrier hp hH hH4 (by omega))
  have hn : cnt P F 0 = 8 := by rcases hR with h | h <;> exact congrArg Row.n h
  have hc := hP.ridge_type_pair_capacity carrier [(6,10,6)] (by decide) hp hfree hF h4 hR (by
    intro t ht u hu
    simp only [List.mem_singleton] at ht hu
    subst t
    subst u
    omega)
  have hk : (G2S4.bcPairs.filter fun R => decide (carrier R)).length = 2 := by decide +kernel
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hk] at hc
  omega

theorem IsCSPolytope5.g2s4_bc_full_local_types
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S4.bRow ∨ faceRow P F = G2S4.cRow) :
    tcnt P F (6,9,5) = 0 ∧ tcnt P F (6,10,6) = 1 ∧ tcnt P F (6,12,8) = 0 ∧
      tcnt P F (7,11,6) = 0 ∧ tcnt P F (7,12,7) = 0 ∧ tcnt P F (7,13,8) = 0 ∧
      tcnt P F (7,14,9) = 0 ∧ tcnt P F (7,15,10) = 0 := by
  have hn : cnt P F 0 = 8 := by rcases hR with h | h <;> exact congrArg Row.n h
  have hr : cnt P F 3 = 8 := by rcases hR with h | h <;> exact congrArg Row.r h
  have hw : q55w P F + 2 * exc P F = 6 := by
    have he := hP.g2s4_bc_weight_eq hp hb hF h4
    rcases hR with h | h <;> rw [h] at he
    · have hh : G2S4.bcWeight G2S4.bRow = 6 := by decide +kernel
      rwa [hh] at he
    · have hh : G2S4.bcWeight G2S4.cRow = 6 := by decide +kernel
      rwa [hh] at he
  have hpr : tcnt P F (6,9,5) = 0 := by
    rcases hR with h | h
    · exact hP.g2s4_bc_b_prism_zero hp hb hF h4 h
    · exact hP.g2s4_bc_c_prism_zero hp hb hF h4 h
  have h610 : tcnt P F (6,10,6) = 1 := by
    have hl : 1 ≤ tcnt P F (6,10,6) := by
      rcases hR with h | h
      · exact hP.g2s4_bc_b_6106_positive hp hb hF h4 h
      · exact hP.g2s4_bc_c_6106_positive hp hb hF h4 h
    have hu := hP.g2s4_bc_6106_le_one hp hF h4 hR
    omega
  have hz : ∀ n e p, 8 ≤ p → tcnt P F (n,e,p) = 0 := by
    intro n e p hpa
    exact hP.tcnt_zero_of_polygon_count hF h4 (by change cnt P F 3 ≤ p; omega)
  have h712 : tcnt P F (7,12,7) = 0 := by
    by_contra hne
    obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (7,12,7))
    simp only [tri3,Prod.mk.injEq] at ht
    have hl := hP.three_ridge_exc_le_weight hT hTF hT3 (by omega) (hP.g2s4_bc_no_big hp F)
    have he := hP.exc_threeface hT hT3
    rw [ht.2.1,ht.2.2] at he
    omega
  exact ⟨hpr,h610,hz 6 12 8 (by omega),hP.eight_ridges_no_7116 hF h4 hn (by omega),
    h712,hz 7 13 8 (by omega),hz 7 14 9 (by omega),hz 7 15 10 (by omega)⟩

theorem IsCSPolytope5.g2s4_bc_b_6117_zero
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hB : faceRow P F = G2S4.bRow) :
    tcnt P F (6,11,7) = 0 := by
  obtain ⟨a,b,c,d,e,f,g,h⟩ := hP.g2s4_bc_full_local_types hp hb hF h4 (Or.inl hB)
  have hn : cnt P F 0 = 8 := congrArg Row.n hB
  have hfp : cnt P F 2 = 19 := congrArg Row.p hB
  have hj : incid P F 0 3 = 38 := congrArg Row.J hB
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  omega

theorem IsCSPolytope5.g2s4_bc_c_6117_zero
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    tcnt P F (6,11,7) = 0 := by
  apply hP.tcnt_zero_of_unique_pair_row hp (R := G2S4.cRow) (by decide +kernel) (6,11,7) _ hF h4
  intro H hH hH4 hne
  rcases hP.g2s4_bc_row_cases hp hH hH4 with hY | hD | hB | hC
  · exact hP.small_rows_6117_zero hH hH4 (by rw [hY]; decide +kernel)
  · have hw := hP.g2s4_bc_weight_eq hp hb hH hH4
    rw [hD] at hw
    have he : G2S4.bcWeight G2S4.dRow = 0 := by decide +kernel
    rw [he] at hw
    exact hP.tcnt_zero_of_small_weight (by decide) (by omega) (by norm_num; omega)
  · exact hP.g2s4_bc_b_6117_zero hp hb hH hH4 hB
  · exact (hne hC).elim

theorem IsCSPolytope5.g2s4_bc_c_pyramids_four
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hC : faceRow P F = G2S4.cRow) :
    tcnt P F (5,8,5) = 4 := by
  obtain ⟨a,b,c,d,e,f,g,h⟩ := hP.g2s4_bc_full_local_types hp hb hF h4 (Or.inr hC)
  have h611 := hP.g2s4_bc_c_6117_zero hp hb hF h4
  have hn : cnt P F 0 = 8 := congrArg Row.n hC
  have hr : cnt P F 3 = 8 := congrArg Row.r hC
  have hfp : cnt P F 2 = 20 := congrArg Row.p hC
  have hj : incid P F 0 3 = 39 := congrArg Row.J hC
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  omega

theorem IsCSPolytope5.g2s4_bc_full_partner
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hF8 : cnt P F 0 = 8) :
    ∃ H T, H ∈ faces P ∧ dim H = 4 ∧ H ≠ F ∧ H ≠ -F ∧ cnt P H 0 = 8 ∧
      T ∈ faces P ∧ dim T = 3 ∧ tri3 P T = (6,10,6) ∧ T = F ∩ H := by
  have hR : faceRow P F = G2S4.bRow ∨ faceRow P F = G2S4.cRow := by
    rcases hP.g2s4_bc_row_cases hp hF h4 with hY | hD | hB | hC
    · have := congrArg Row.n hY; change cnt P F 0 = 7 at this; omega
    · have := congrArg Row.n hD; change cnt P F 0 = 7 at this; omega
    · exact Or.inl hB
    · exact Or.inr hC
  have h610 := (hP.g2s4_bc_full_local_types hp hb hF h4 hR).2.1
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (6,10,6))
  obtain ⟨H,hH,hH4,hHF,hTH⟩ := hP.exists_other_facet hT hT3 hTF
  have hpos := hP.one_le_tcnt hT hTH hT3
  rw [ht] at hpos
  have hHR := hP.g2s4_bc_6106_carrier hp hH hH4 hpos
  have hH8 : cnt P H 0 = 8 := by rcases hHR with h | h <;> exact congrArg Row.n h
  have hHnF : H ≠ -F := by
    intro he
    obtain ⟨x,hx⟩ := hT.1
    have hd := hP.facet_disjoint_neg hF h4
    exact Set.disjoint_left.1 hd (hTF hx) (he ▸ hTH hx)
  exact ⟨H,T,hH,hH4,hHF,hHnF,hH8,hT,hT3,ht,
    hP.three_face_eq_inter hF h4 hH hH4 hHF.symm hT hT3 hTF hTH⟩

end Kalai5

