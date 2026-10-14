import Kalai5.Endpoints.Q55.RowWeights

/-!
# Q55 weight four for B

Weight three would force three quadrilaterals and two of type (5,5).
The twelve ridge counts then force either the already excluded six-pyramid
configuration or a six-vertex ridge with two quadrilaterals. Those two cannot
be of type (5,5), leaving too few quadrilaterals. The old weight tables remain
unchanged so their saved certificates retain their exact interpretation.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.big2_mono_of_subset {T F : Set E5} (hTF : T ⊆ F) : big2 P T ≤ big2 P F :=
  Set.ncard_le_ncard (fun _ hQ => ⟨hQ.1, hQ.2.1.trans hTF, hQ.2.2⟩)
    (hP.faces_finite.subset fun _ hQ => hQ.1)

set_option maxHeartbeats 2000000 in
/-- B has Q55 weight at least four, without a zero-stress assumption. -/
theorem IsCSPolytope5.q55_b_four {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8, 19, 19, 8, 38⟩) :
    4 ≤ q55w P F + 2 * exc P F := by
  have hR' := hR
  simp only [faceRow, Row.mk.injEq] at hR'
  obtain ⟨hn, he, hp, hr, hJ⟩ := hR'
  obtain ⟨c1, c2, c3, -⟩ := hP.facet8_arith hF h4 hn
  have hweight := hP.q55_b_three hF h4 hR
  have hbound := hP.q4_add_big_le_exc F
  have hw := hP.q55w_ge F
  have hb := hP.two_b55_le hF h4
  have hq := hP.q55w_eq_b55 F
  have hexc := hP.exc_eq_faceRow hF h4
  rw [hR] at hexc
  norm_num at hexc
  by_contra hbad
  have hq3 : q4 P F = 3 := by
    have hq2 : 2 ≤ q4 P F := by omega
    have hb0 : big2 P F = 0 := by omega
    have hex := hP.exc_eq_q4_of_big F hb0
    omega
  have hb0 : big2 P F = 0 := by omega
  have hb2 : (b55set P F).ncard = 2 := by omega
  have hy4 : 4 ≤ tcnt P F (5, 8, 5) := by omega
  by_cases hy6 : 6 ≤ tcnt P F (5, 8, 5)
  · have ht : tcnt P F (4, 6, 4) = 2 := by omega
    have hy : tcnt P F (5, 8, 5) = 6 := by omega
    apply hP.not_two_tetrahedra_pyramids hF h4 ht
    intro T hT hTF hT3
    have h1 := hP.one_le_tcnt hT hTF hT3
    have hne : T ≠ F := by rintro rfl; omega
    have hlt := hP.cnt_zero_lt hT hF hTF hne
    have hin := hP.tri3_mem_fv8 hT hT3 (by omega)
    simp only [fv8, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at h1 ⊢ <;>
      first | (left; rfl) | (right; rfl) | omega
  · have hc : 1 ≤ tcnt P F (6, 10, 6) := by
      have h7 : tcnt P F (7, 11, 6) + tcnt P F (7, 12, 7) + tcnt P F (7, 13, 8) +
          tcnt P F (7, 14, 9) + tcnt P F (7, 15, 10) = 0 := by omega
      have hy45 : tcnt P F (5, 8, 5) = 4 ∨ tcnt P F (5, 8, 5) = 5 := by omega
      rcases hy45 with hy | hy <;> omega
    obtain ⟨T, hT, hTF, hT3, ht⟩ := hP.exists_of_tcnt hc
    have ht' := ht
    simp only [tri3, Prod.mk.injEq] at ht'
    have hbt : big2 P T = 0 := by have := hP.big2_mono_of_subset hTF; omega
    have het := hP.exc_threeface hT hT3
    rw [ht'.2.1, ht'.2.2] at het
    have heq := hP.exc_eq_q4_of_big T hbt
    have hqt : q4 P T = 2 := by omega
    have hres := hP.b55_add_q4_le hT hTF hT3 (by omega)
    omega

omit hP in
/-- A separate table preserves all earlier certificate formats and weights. -/
def q55RefinedRowWeight (R : Row) : ℕ :=
  if R = ⟨8, 19, 19, 8, 38⟩ then 4 else q55StrongRowWeight R

omit hP in
lemma q55StrongRowWeight_le_refined (R : Row) : q55StrongRowWeight R ≤ q55RefinedRowWeight R := by
  unfold q55RefinedRowWeight
  split_ifs with h
  · subst R; decide
  · exact le_rfl

theorem IsCSPolytope5.q55_refined_row_weight {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) :
    (q55RefinedRowWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold q55RefinedRowWeight
  split_ifs with h
  · exact hP.q55_b_four hF h4 h
  · exact hP.q55_strong_row_weight hF h4

theorem IsCSPolytope5.q55_refined_rows (hv : fvec P 0 = 16) :
    (((facetRows P).map q55RefinedRowWeight).sum : ℤ) ≤
      4 * (flagDataOf P).A + 2 * (((flagDataOf P).f024 : ℤ) - 3 * (flagDataOf P).y) := by
  rw [hP.facetRows_sum q55RefinedRowWeight, Nat.cast_sum]
  calc ∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55RefinedRowWeight (faceRow P F) : ℤ)
      ≤ ∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F) := by
        refine Finset.sum_le_sum fun F hF => ?_
        rw [Set.Finite.mem_toFinset] at hF
        exact hP.q55_refined_row_weight hF.1 hF.2
    _ ≤ _ := hP.q55 hv

end Kalai5
