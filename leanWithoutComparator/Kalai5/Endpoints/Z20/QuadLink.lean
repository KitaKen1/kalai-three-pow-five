import Kalai5.Endpoints.Z20.QuadRows

/-!
# The quadrilateral-link inequality

Let `Q` be a quadrilateral 2-face of `P`, lying in `ℓ(Q) ≥ 3` facets.  A facet with row `Y` or `E`
(`goodRow`) through `Q` contains exactly one 3-face through `Q` with five vertices
(`IsCSPolytope5.good_five_one`); every 3-face lies in exactly two facets, so the number of pairs
(facet, five-vertex 3-face) through `Q` is even (`IsCSPolytope5.sum_five_eq_two`).  Hence if all
facets through `Q` are good, `ℓ(Q)` is even and at least four, and in general, with `g` good
facets through `Q`, `g - 2(ℓ - g) ≤ 4(ℓ - 3)` (`IsCSPolytope5.quad_ineq`).

Weighting each facet by `q4` if it is good and by `-2 q4` otherwise and summing over the
quadrilaterals gives `Σ_F w(F) ≤ 4A`; with `q4(Y) = 3`, `exc(E) = 2` and `q4 ≤ exc`:

    9 #Y + 4 #E ≤ 4 A + 2 (f₀₂₄ - 3 f₂₄)          (`IsCSPolytope5.quadLink`)
-/

namespace Kalai5

open Set

open scoped Classical

/-- Rows `Y` and `E`. -/
def goodRow (R : Row) : Prop := R = excRow ∨ R = eRow

/-- The weight `9 [R = Y] + 4 [R = E]`. -/
def qlWeight (R : Row) : ℕ := if R = excRow then 9 else if R = eRow then 4 else 0

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.above_finite (G : Set E5) (k : ℕ) :
    {F | F ∈ faces P ∧ G ⊆ F ∧ dim F = k}.Finite :=
  hP.faces_finite.subset fun F hF => hF.1

/-- In a facet `Y` or `E` every quadrilateral lies in exactly one 3-face with five vertices. -/
lemma IsCSPolytope5.good_five_one {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hg : goodRow (faceRow P F)) {Q : Set E5} (hQ : Q ∈ faces P) (hQF : Q ⊆ F)
    (h2 : dim Q = 2) (h4Q : cnt P Q 0 = 4) :
    ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T ∧ cnt P T 0 = 5).card = 1 := by
  rcases hg with h | h
  · exact (hP.Y_quad hF h4 h).2.2 Q hQ hQF h2 h4Q
  · exact (hP.E_quad hF h4 h).2 Q hQ hQF h2 h4Q

/-- **Parity around a face**: pairs (facet `F ⊇ Q`, five-vertex 3-face `Q ⊆ T ⊆ F`) are counted
twice over the 3-faces. -/
lemma IsCSPolytope5.sum_five_eq_two {Q : Set E5} (hQ : Q ∈ faces P) :
    ∑ F ∈ (hP.above_finite Q 4).toFinset,
      ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T ∧ cnt P T 0 = 5).card =
    2 * ((hP.above_finite Q 3).toFinset.filter fun T => cnt P T 0 = 5).card := by
  simp only [Finset.card_eq_sum_ones]
  rw [Finset.sum_comm' (t' := (hP.above_finite Q 3).toFinset.filter fun T => cnt P T 0 = 5)
    (s' := fun T => (hP.above_finite T 4).toFinset)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hT
    rw [← Finset.card_eq_sum_ones, ← Set.ncard_eq_toFinset_card _ (hP.above_finite T 4),
      hP.ridge_two hT.1.1 hT.1.2.2, mul_one]
  · intro F T
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hF, hQF, hF4⟩, ⟨hT, hTF, hT3⟩, hQT, h5⟩
      exact ⟨⟨hF, hTF, hF4⟩, ⟨hT, hQT, hT3⟩, h5⟩
    · rintro ⟨⟨hF, hTF, hF4⟩, ⟨hT, hQT, hT3⟩, h5⟩
      exact ⟨⟨hF, hQT.trans hTF, hF4⟩, ⟨hT, hTF, hT3⟩, hQT, h5⟩

/-- **The inequality at one quadrilateral**: `g - 2(ℓ - g) ≤ 4(ℓ - 3)`. -/
lemma IsCSPolytope5.quad_ineq {Q : Set E5} (hQ : Q ∈ faces P) (h2 : dim Q = 2)
    (h4Q : cnt P Q 0 = 4) :
    ∑ F ∈ (hP.above_finite Q 4).toFinset, (if goodRow (faceRow P F) then (1 : ℤ) else -2) ≤
      4 * (((hP.above_finite Q 4).toFinset.card : ℤ) - 3) := by
  have hℓ : 3 ≤ (hP.above_finite Q 4).toFinset.card := by
    have := hP.three_le_up hQ h2
    rwa [Set.ncard_eq_toFinset_card _ (hP.above_finite Q 4)] at this
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (hP.above_finite Q 4).toFinset) (fun F => goodRow (faceRow P F))
  by_cases hall : ((hP.above_finite Q 4).toFinset.filter fun F => goodRow (faceRow P F)).card =
      (hP.above_finite Q 4).toFinset.card
  · have hgood : ∀ F ∈ (hP.above_finite Q 4).toFinset, goodRow (faceRow P F) :=
      Finset.filter_card_eq hall
    have hpar := hP.sum_five_eq_two hQ
    have hone : ∀ F ∈ (hP.above_finite Q 4).toFinset,
        ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T ∧ cnt P T 0 = 5).card = 1 := by
      intro F hF
      have hF' := hF
      rw [Set.Finite.mem_toFinset] at hF'
      exact hP.good_five_one hF'.1 hF'.2.2 (hgood F hF) hQ hF'.2.1 h2 h4Q
    rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one] at hpar
    push_cast
    omega
  · have hlt := lt_of_le_of_ne (Finset.card_filter_le _ _) hall
    push_cast
    omega

/-- The facet weight dominates `9 [Y] + 4 [E]` up to `2 exc`. -/
lemma IsCSPolytope5.weight_ge {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (qlWeight (faceRow P F) : ℤ) ≤
      (if goodRow (faceRow P F) then (1 : ℤ) else -2) * q4 P F + 2 * exc P F := by
  by_cases hY : faceRow P F = excRow
  · obtain ⟨h1, h2, -⟩ := hP.Y_quad hF h4 hY
    rw [if_pos (show goodRow (faceRow P F) from Or.inl hY), h1, h2, hY]
    simp [qlWeight]
  · by_cases hE : faceRow P F = eRow
    · obtain ⟨h2, -⟩ := hP.E_quad hF h4 hE
      have hq : (0 : ℤ) ≤ q4 P F := by positivity
      have hw : qlWeight (faceRow P F) = 4 := by
        rw [hE]; decide
      rw [if_pos (show goodRow (faceRow P F) from Or.inr hE), h2, hw]
      push_cast
      linarith
    · have hw : qlWeight (faceRow P F) = 0 := by simp [qlWeight, hY, hE]
      rw [hw, if_neg (by rintro (h | h) <;> contradiction)]
      have h1 := hP.q4_add_big_le_exc F
      have : (0 : ℤ) ≤ big2 P F := by positivity
      push_cast
      linarith

/-- The total excess: `Σ_F exc F = f₀₂₄ - 3 f₂₄`. -/
lemma IsCSPolytope5.sum_exc :
    ∑ F ∈ (hP.kfaces_finite 4).toFinset, exc P F =
      ((flagDataOf P).f024 : ℤ) - 3 * (flagDataOf P).y := by
  simp only [flagDataOf]
  rw [hP.flag3_eq_sum_last 0 2 4, hP.flag2_eq_sum 2 4]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rfl

/-- **The weighted quadrilateral count**: `Σ_F w(F) ≤ 4A`. -/
lemma IsCSPolytope5.sum_weight_le :
    ∑ F ∈ (hP.kfaces_finite 4).toFinset,
      (if goodRow (faceRow P F) then (1 : ℤ) else -2) * q4 P F ≤ 4 * (flagDataOf P).A := by
  have hexp : ∀ F, (if goodRow (faceRow P F) then (1 : ℤ) else -2) * q4 P F =
      ∑ Q ∈ (hP.below_finite F 2).toFinset,
        if cnt P Q 0 = 4 then (if goodRow (faceRow P F) then (1 : ℤ) else -2) else 0 := by
    intro F
    rw [hP.q4_eq_card, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl fun F _ => hexp F]
  rw [Finset.sum_comm' (t' := (hP.kfaces_finite 2).toFinset)
    (s' := fun Q => (hP.above_finite Q 4).toFinset)]
  · rw [hP.A_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun Q hQ => ?_
    rw [Set.Finite.mem_toFinset] at hQ
    have h3 := hP.three_le_cnt hQ.1 hQ.2
    have hl := hP.three_le_up hQ.1 hQ.2
    rw [Set.ncard_eq_toFinset_card _ (hP.above_finite Q 4)] at hl ⊢
    by_cases h4Q : cnt P Q 0 = 4
    · rw [Finset.sum_congr rfl fun F _ => if_pos h4Q]
      have := hP.quad_ineq hQ.1 hQ.2 h4Q
      rw [h4Q]
      push_cast
      linarith
    · rw [Finset.sum_congr rfl fun F _ => if_neg h4Q, Finset.sum_const_zero]
      have : (0 : ℤ) ≤ ((cnt P Q 0 : ℤ) - 3) *
          (((hP.above_finite Q 4).toFinset.card : ℤ) - 3) :=
        mul_nonneg (by omega) (by omega)
      linarith
  · intro F Q
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    tauto

/-- **The quadrilateral-link inequality** `9 #Y + 4 #E ≤ 4 A + 2 (f₀₂₄ - 3 f₂₄)`. -/
theorem IsCSPolytope5.quadLink :
    ((((facetRows P).map qlWeight).sum : ℕ) : ℤ) ≤
      4 * (flagDataOf P).A + 2 * (((flagDataOf P).f024 : ℤ) - 3 * (flagDataOf P).y) := by
  rw [hP.facetRows_sum qlWeight, Nat.cast_sum, ← hP.sum_exc]
  calc ∑ F ∈ (hP.kfaces_finite 4).toFinset, (qlWeight (faceRow P F) : ℤ)
      ≤ ∑ F ∈ (hP.kfaces_finite 4).toFinset,
          ((if goodRow (faceRow P F) then (1 : ℤ) else -2) * q4 P F + 2 * exc P F) := by
        refine Finset.sum_le_sum fun F hF => ?_
        rw [Set.Finite.mem_toFinset] at hF
        exact hP.weight_ge hF.1 hF.2
    _ = ∑ F ∈ (hP.kfaces_finite 4).toFinset,
          (if goodRow (faceRow P F) then (1 : ℤ) else -2) * q4 P F
          + 2 * ∑ F ∈ (hP.kfaces_finite 4).toFinset, exc P F := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        have := hP.sum_weight_le
        linarith

end cs

end Kalai5
