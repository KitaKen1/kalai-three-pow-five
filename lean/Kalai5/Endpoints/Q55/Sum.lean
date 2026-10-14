import Kalai5.Endpoints.Q55.Quad

/-!
# The (5,5)-quadrilateral inequality

For a facet `H` let `q55w H = Σ_{Q ⊆ H quadrilateral} (if (5,5) at Q then -2 else 1)`, that is
`q₄(H) - 3 b₅₅(H)`.  Summing `IsCSPolytope5.quad55_ineq` over the quadrilaterals (sixteen
vertices):

  `Σ_H q55w H ≤ 4 A`                                        (`IsCSPolytope5.sum_q55w_le`),

hence `Σ_H (q55w H + 2 exc H) ≤ 4A + 2(f₀₂₄ - 3f₂₄)` with nonnegative summands
(`IsCSPolytope5.q55`).  The local lower bounds of `q55w + 2 exc` for particular facet types are the
row weights of the LP.
-/

namespace Kalai5

open Set

open scoped Classical

/-- The (5,5)-weight of a facet: `q₄ - 3 b₅₅`. -/
noncomputable def q55w (P H : Set E5) : ℤ :=
  ∑ᶠ Q ∈ {Q | Q ∈ faces P ∧ Q ⊆ H ∧ dim Q = 2 ∧ cnt P Q 0 = 4},
    (if non5 P H Q = ∅ then (-2 : ℤ) else 1)

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- `q55w` as a finset sum over the 2-faces of `H`. -/
lemma IsCSPolytope5.q55w_eq (H : Set E5) :
    q55w P H = ∑ Q ∈ (hP.below_finite H 2).toFinset,
      (if cnt P Q 0 = 4 then (if non5 P H Q = ∅ then (-2 : ℤ) else 1) else 0) := by
  unfold q55w
  rw [← Finset.sum_filter]
  have hfin : {Q | Q ∈ faces P ∧ Q ⊆ H ∧ dim Q = 2 ∧ cnt P Q 0 = 4}.Finite :=
    hP.faces_finite.subset fun Q hQ => hQ.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  apply Finset.sum_congr
  · ext Q
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_ofPred_eq]
    tauto
  · intro _ _; rfl

/-- `q55w ≥ -2 q₄`. -/
lemma IsCSPolytope5.q55w_ge (H : Set E5) : -2 * (q4 P H : ℤ) ≤ q55w P H := by
  rw [hP.q55w_eq, hP.q4_eq_card, ← Finset.sum_filter]
  have : ∀ Q ∈ (hP.below_finite H 2).toFinset.filter (fun Q => cnt P Q 0 = 4),
      (-2 : ℤ) ≤ (if non5 P H Q = ∅ then (-2 : ℤ) else 1) := by
    intro Q _; split_ifs <;> norm_num
  have h := Finset.sum_le_sum this
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at h
  linarith

/-- **The weighted quadrilateral count**: `Σ_H q55w H ≤ 4A` (sixteen vertices). -/
lemma IsCSPolytope5.sum_q55w_le (h16 : fvec P 0 = 16) :
    ∑ H ∈ (hP.kfaces_finite 4).toFinset, q55w P H ≤ 4 * (flagDataOf P).A := by
  rw [Finset.sum_congr rfl fun H _ => hP.q55w_eq H]
  rw [Finset.sum_comm' (t' := (hP.kfaces_finite 2).toFinset)
    (s' := fun Q => (hP.above_finite Q 4).toFinset)]
  · rw [hP.A_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun Q hQ => ?_
    rw [Set.Finite.mem_toFinset] at hQ
    have h3 := hP.three_le_cnt hQ.1 hQ.2
    have hl := hP.three_le_up hQ.1 hQ.2
    rw [Set.ncard_eq_toFinset_card _ (hP.above_finite Q 4)] at hl ⊢
    by_cases h4Q : cnt P Q 0 = 4
    · rw [Finset.sum_congr rfl fun H _ => if_pos h4Q]
      have := hP.quad55_ineq h16 hQ.1 hQ.2 h4Q
      rw [h4Q]
      push_cast
      linarith
    · rw [Finset.sum_congr rfl fun H _ => if_neg h4Q, Finset.sum_const_zero]
      have : (0 : ℤ) ≤ ((cnt P Q 0 : ℤ) - 3) *
          (((hP.above_finite Q 4).toFinset.card : ℤ) - 3) :=
        mul_nonneg (by omega) (by omega)
      linarith
  · intro H Q
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    tauto

/-- **The (5,5)-quadrilateral inequality** with excess:
`Σ_H (q55w H + 2 exc H) ≤ 4A + 2(f₀₂₄ - 3f₂₄)`. -/
theorem IsCSPolytope5.q55 (h16 : fvec P 0 = 16) :
    ∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H) ≤
      4 * (flagDataOf P).A + 2 * (((flagDataOf P).f024 : ℤ) - 3 * (flagDataOf P).y) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hP.sum_exc]
  have := hP.sum_q55w_le h16
  linarith

/-- Each summand is nonnegative: `q55w H + 2 exc H ≥ 0`. -/
lemma IsCSPolytope5.q55w_add_exc_nonneg (H : Set E5) : 0 ≤ q55w P H + 2 * exc P H := by
  have h1 := hP.q55w_ge H
  have h2 := hP.q4_add_big_le_exc H
  have : (0 : ℤ) ≤ big2 P H := by positivity
  linarith

end cs

end Kalai5
