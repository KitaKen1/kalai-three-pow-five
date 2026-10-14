import Kalai5.Endpoints.FacetCarrierCapacity

namespace Kalai5
open Set
open scoped Classical

namespace G2S2
def r0Pairs : List Row := [excRow,excRow,excRow,G2S4.aRow,G2S4.aRow,G2S4.aRow,G2S4.aRow,r35Row,r0Row]
end G2S2

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A square-pyramid ridge gives A a quadrilateral. At excess two this
excludes a pentagon, so A must pay weight six. -/
theorem IsCSPolytope5.a_weight_six_of_pyramid {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = G2S4.aRow)
    (ht : 1 ≤ tcnt P F (5,8,5)) : q55w P F + 2 * exc P F = 6 := by
  obtain ⟨T,hT,hTF,hT3,htype⟩ := hP.exists_of_tcnt ht
  have hqT := (hP.q4_585 hT hT3 htype).1
  have hm : q4 P T ≤ q4 P F := Set.ncard_le_ncard
    (by intro Q hQ; exact ⟨hQ.1,hQ.2.1.trans hTF,hQ.2.2⟩)
    (hP.faces_finite.subset fun Q hQ => hQ.1)
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num [G2S4.aRow] at he
  have hbound := hP.q4_add_big_le_exc F
  exact hP.a_weight_six_of_no_big hF h4 hR (by omega)

/-- The baseline costs 140 out of 144. Only two actual A facets can
spend the extra two units required by a square-pyramid ridge. -/
theorem IsCSPolytope5.g2s2_r0_heavy_a_card_le_two
    (hp : (facetRows P).Perm (G2S2.r0Pairs ++ G2S2.r0Pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 144) :
    ((hP.kfaces_finite 4).toFinset.filter fun H =>
      faceRow P H = G2S4.aRow ∧ 6 ≤ q55w P H + 2 * exc P H).card ≤ 2 := by
  let active : Set E5 → Prop := fun H => faceRow P H = G2S4.aRow ∧ 6 ≤ q55w P H + 2 * exc P H
  have hbase : (∑ H ∈ (hP.kfaces_finite 4).toFinset,
      (PrismBudget.contextRowWeight G2S2.r0Pairs (faceRow P H) : ℤ)) = 140 := by
    have hs : ((facetRows P).map (PrismBudget.contextRowWeight G2S2.r0Pairs)).sum = 140 := by
      rw [(hp.map _).sum_eq]
      decide +kernel
    rw [hP.facetRows_sum] at hs
    exact_mod_cast hs
  have hl : ∀ H ∈ (hP.kfaces_finite 4).toFinset,
      (PrismBudget.contextRowWeight G2S2.r0Pairs (faceRow P H) : ℤ) +
        (if active H then 2 else 0) ≤ q55w P H + 2 * exc P H := by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    split_ifs with ha
    · have hh := ha.2
      rw [ha.1]
      have hf : PrismBudget.contextRowWeight G2S2.r0Pairs G2S4.aRow = 4 := by decide +kernel
      rw [hf]
      omega
    · simpa only [add_zero] using hP.context_row_weight_lower hp hH.1 hH.2
  have hsum := (Finset.sum_le_sum hl).trans hb
  rw [Finset.sum_add_distrib,hbase] at hsum
  have hi : (∑ H ∈ (hP.kfaces_finite 4).toFinset, if active H then (2 : ℤ) else 0) =
      2 * ((hP.kfaces_finite 4).toFinset.filter active).card := by
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H hH
    split_ifs <;> norm_num
  rw [hi] at hsum
  change ((hP.kfaces_finite 4).toFinset.filter active).card ≤ 2
  omega

/-- A weight-aware carrier count excludes the R0 candidate without
formalizing the exploratory parity DP. -/
theorem IsCSPolytope5.g2s2_r0_capacity_false
    (hp : (facetRows P).Perm (G2S2.r0Pairs ++ G2S2.r0Pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 144) : False := by
  let Fs := (hP.kfaces_finite 4).toFinset
  let carrier : Set E5 → Prop := fun H => faceRow P H ≠ G2S4.aRow ∨ 6 ≤ q55w P H + 2 * exc P H
  have hneg : ∀ H ∈ faces P, dim H = 4 → carrier H → carrier (-H) := by
    intro H hH hH4 hc
    simpa only [carrier,hP.faceRow_neg,hP.actual_weight_neg] using hc
  have hm : r0Row ∈ facetRows P := hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel))
  obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows hm
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  let types : List (ℕ × ℕ × ℕ) := [(5,8,5),(6,9,5)]
  let A := (hP.below_finite F 3).toFinset.filter fun T => tri3 P T ∈ types
  have hA : ∀ T ∈ A, T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 := by
    intro T hT
    have hh := (Finset.mem_filter.1 hT).1
    rwa [Set.Finite.mem_toFinset] at hh
  have htypes : ∀ T ∈ A, tri3 P T = (5,8,5) ∨ tri3 P T = (6,9,5) := by
    intro T hT
    simpa only [types,List.mem_cons,List.not_mem_nil,or_false] using (Finset.mem_filter.1 hT).2
  have hwide : ∀ T ∈ A, ∀ U ∈ A, cnt P F 0 < cnt P T 0 + cnt P U 0 := by
    intro T hT U hU
    have hT5 : 5 ≤ cnt P T 0 := by
      rcases htypes T hT with h | h <;> have := congrArg Prod.fst h <;> change cnt P T 0 = _ at this <;> omega
    have hU5 : 5 ≤ cnt P U 0 := by
      rcases htypes U hU with h | h <;> have := congrArg Prod.fst h <;> change cnt P U 0 = _ at this <;> omega
    omega
  have hcar : ∀ T ∈ A, ∀ H ∈ faces P, dim H = 4 → T ⊆ H → carrier H := by
    intro T hTA H hH hH4 hTH
    by_cases hHA : faceRow P H = G2S4.aRow
    · apply Or.inr
      have ht := hP.one_le_tcnt (hA T hTA).1 hTH (hA T hTA).2.2
      rcases htypes T hTA with hpy | hpr
      · rw [hpy] at ht
        exact (hP.a_weight_six_of_pyramid hH hH4 hHA ht).ge
      · rw [hpr] at ht
        have hz := hP.small_rows_prism_free hH hH4 (by rw [hHA]; decide +kernel)
        omega
    · exact Or.inl hHA
  have hFC : carrier F := Or.inl (by rw [hR]; decide +kernel)
  have hcap := hP.ridge_facet_predicate_capacity carrier hneg hF h4 hFC A hA hwide hcar
  obtain ⟨_,hpy,hpr,_,_,_⟩ := hP.r0_types hF h4 hR
  have hAc : A.card = 6 := by
    have he := hP.tcnt_list_sum_eq_card F types (by decide)
    change (types.map (tcnt P F)).sum = A.card at he
    simp only [types,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hpy,hpr] at he
    omega
  have hbase : (Fs.filter fun H => faceRow P H ≠ G2S4.aRow).card = 10 := by
    have hs : ((facetRows P).map fun R => if R ≠ G2S4.aRow then 1 else 0).sum = 10 := by
      rw [(hp.map _).sum_eq]
      decide +kernel
    rw [hP.facetRows_sum] at hs
    simpa only [Fs,Finset.card_filter] using hs
  have hsplit : Fs.filter carrier = (Fs.filter fun H => faceRow P H ≠ G2S4.aRow) ∪
      (Fs.filter fun H => faceRow P H = G2S4.aRow ∧ 6 ≤ q55w P H + 2 * exc P H) := by
    ext H
    simp only [Finset.mem_filter,Finset.mem_union,carrier]
    tauto
  have hupper := Finset.card_union_le
    (Fs.filter fun H => faceRow P H ≠ G2S4.aRow)
    (Fs.filter fun H => faceRow P H = G2S4.aRow ∧ 6 ≤ q55w P H + 2 * exc P H)
  have hheavy := hP.g2s2_r0_heavy_a_card_le_two hp hb
  change (Fs.filter fun H => faceRow P H = G2S4.aRow ∧ 6 ≤ q55w P H + 2 * exc P H).card ≤ 2 at hheavy
  change 2 * A.card + 2 ≤ (Fs.filter carrier).card at hcap
  rw [hAc,hsplit] at hcap
  rw [hbase] at hupper
  omega

end Kalai5
