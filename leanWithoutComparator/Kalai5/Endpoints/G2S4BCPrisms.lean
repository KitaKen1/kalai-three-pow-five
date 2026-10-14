import Kalai5.Endpoints.G2S4Profiles
import Kalai5.Endpoints.BSupportBudget

namespace Kalai5
open Set
open scoped Classical

namespace G2S4
def bcWeight (R : Row) : ℕ := if R = cRow then 6 else q55QFourRowWeight R
end G2S4

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.tcnt_neg (F : Set E5) (t : ℕ × ℕ × ℕ) :
    tcnt P (-F) t = tcnt P F t := by
  have ht : ∀ Q, tri3 P (-Q) = tri3 P Q := by intro Q; simp only [tri3,hP.cnt_neg]
  have hs : {Q | Q ∈ faces P ∧ Q ⊆ -F ∧ dim Q = 3 ∧ tri3 P Q = t} =
      (fun Q : Set E5 => -Q) '' {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 3 ∧ tri3 P Q = t} := by
    ext Q
    constructor
    · rintro ⟨hQ,hQF,h3,hqt⟩
      exact ⟨-Q,⟨neg_mem_faces hP.symm hQ,neg_subset_iff.1 hQF,
        by rw [dim_neg,h3],by rw [ht,hqt]⟩,neg_neg Q⟩
    · rintro ⟨Q,⟨hQ,hQF,h3,hqt⟩,rfl⟩
      exact ⟨neg_mem_faces hP.symm hQ,Set.neg_subset_neg.2 hQF,
        by rw [dim_neg,h3],by rw [ht,hqt]⟩
  rw [tcnt,tcnt,hs,Set.ncard_image_of_injective _ neg_injective]

theorem IsCSPolytope5.g2s4_bc_row_cases
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    faceRow P F = excRow ∨ faceRow P F = G2S4.dRow ∨
      faceRow P F = G2S4.bRow ∨ faceRow P F = G2S4.cRow := by
  have hm := hP.faceRow_mem_pair_rows hp hF h4
  simpa only [G2S4.bcPairs,List.mem_cons,List.not_mem_nil,or_false,or_self_left] using hm

theorem IsCSPolytope5.g2s4_bc_no_big
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs)) (F : Set E5) : big2 P F = 0 := by
  let carrier : Row → Prop := fun R => R = G2S4.bRow ∨ R = G2S4.cRow
  apply hP.big2_zero_of_pair_support carrier hp (by decide +kernel) _ F
  intro H hH hH4 hf
  rcases hP.g2s4_bc_row_cases hp hH hH4 with hY | hD | hB | hC
  · have he := hP.exc_eq_faceRow hH hH4
    rw [hY] at he
    norm_num [excRow] at he
    have ht := hP.Y_prism_count hH hH4 hY
    exact hP.big2_zero_of_prism_exc_le_four (by omega) (by omega)
  · have he := hP.exc_eq_faceRow hH hH4
    rw [hD] at he
    norm_num [G2S4.dRow] at he
    have hb := hP.q4_add_big_le_exc H
    omega
  · exact (hf (Or.inl hB)).elim
  · exact (hf (Or.inr hC)).elim

theorem IsCSPolytope5.g2s4_bc_c_upper
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hC : faceRow P F = G2S4.cRow) :
    q55w P F + 2 * exc P F ≤ 6 := by
  have hu := hP.facet_weight_le_context_upper hp (S := 4) (by simpa using hb) hF h4
  rw [hC] at hu
  have he : PrismBudget.contextUpper 4 G2S4.bcPairs G2S4.cRow = 6 := by decide +kernel
  rwa [he] at hu

theorem IsCSPolytope5.g2s4_bc_c_prism_zero
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hC : faceRow P F = G2S4.cRow) :
    tcnt P F (6,9,5) = 0 := by
  have hu := hP.g2s4_bc_c_upper hp hb hF h4 hC
  by_contra hz
  have hn : cnt P F 0 = 8 := congrArg Row.n hC
  have hl := (hP.prism_weight_lower hF h4 hn (by omega)).2
  rw [hC] at hl
  norm_num [G2S4.cRow,PrismBudget.prismLower,PrismBudget.rowExcess] at hl
  omega

/-- The six Y pairs contribute an even prism count. A prism in the single
B pair would make the pair count odd, since C cannot afford one. -/
theorem IsCSPolytope5.g2s4_bc_b_prism_zero
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hB : faceRow P F = G2S4.bRow) :
    tcnt P F (6,9,5) = 0 := by
  by_contra hz
  have he := hP.exc_eq_faceRow hF h4
  rw [hB] at he
  norm_num [G2S4.bRow] at he
  have hc := hP.prism_count_le_one_of_exc_le_four (by omega : exc P F ≤ 4)
  have hone : tcnt P F (6,9,5) = 1 := by omega
  have htwo : ((facetRows P).map fun R => if R = G2S4.bRow then 1 else 0).sum = 2 := by
    rw [(hp.map _).sum_eq]
    decide +kernel
  let value : Row → ℕ := fun R => if R = excRow ∨ R = G2S4.bRow then 1 else 0
  have hlocal : ∀ H ∈ faces P, dim H = 4 → (fun _ : Row => true) (faceRow P H) = true →
      tcnt P H (6,9,5) = value (faceRow P H) := by
    intro H hH hH4 _
    rcases hP.g2s4_bc_row_cases hp hH hH4 with hY | hD | hBr | hC
    · rw [hP.Y_prism_count hH hH4 hY,hY]
      rfl
    · rw [hP.small_rows_prism_free hH hH4 (by rw [hD]; decide +kernel),hD]
      rfl
    · have heq := hP.two_row_facets_eq_or_neg htwo hF h4 hB hH hH4 hBr
      have ht : tcnt P H (6,9,5) = 1 := by
        rcases heq with heq | heq
        · rwa [heq]
        · rw [heq,hP.tcnt_neg,hone]
      rw [ht,hBr]
      decide +kernel
    · rw [hP.g2s4_bc_c_prism_zero hp hb hH hH4 hC,hC]
      rfl
  have hpar := hP.facet_count_pair_row_parity (fun H => tcnt P H (6,9,5)) value
    (fun _ => true) hp hlocal (hP.four_dvd_sum_tcnt (6,9,5))
  have hbad : PrismBudget.rowParityOK value (fun _ => true) G2S4.bcPairs = false := by decide +kernel
  rw [hbad] at hpar
  contradiction

set_option maxHeartbeats 2000000 in
/-- The low-weight B argument only uses the absence of prisms. -/
theorem IsCSPolytope5.b_no_prism_special_ridge {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = G2S4.bRow)
    (hpr : tcnt P F (6,9,5) = 0) :
    1 ≤ tcnt P F (6,10,6) ∨ 1 ≤ tcnt P F (7,12,7) := by
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hr : cnt P F 3 = 8 := congrArg Row.r hR
  have hp : cnt P F 2 = 19 := congrArg Row.p hR
  have hj : incid P F 0 3 = 38 := congrArg Row.J hR
  have h7 := hP.eight_ridges_no_7116 hF h4 hn (by omega)
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  by_contra hbad
  have h610 : tcnt P F (6,10,6) = 0 := by omega
  have h712 : tcnt P F (7,12,7) = 0 := by omega
  have ht : tcnt P F (4,6,4) = 2 := by omega
  have hpy : tcnt P F (5,8,5) = 6 := by omega
  apply hP.not_two_tetrahedra_pyramids hF h4 ht
  intro T hT hTF hT3
  have hlt := hP.cnt_zero_lt hT hF hTF (by intro he; rw [he,h4] at hT3; omega)
  have hm := hP.tri3_mem_fv8 hT hT3 (by omega)
  have hpos := hP.one_le_tcnt hT hTF hT3
  simp only [fv8,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  all_goals rw [h] at hpos; omega

end Kalai5
