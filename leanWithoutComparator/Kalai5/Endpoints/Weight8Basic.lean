import Kalai5.Endpoints.FullCoverStress

/-!
# Elementary Q55 weights from the twelve 3-face counts

The three weights below only use the numbers of square pyramids and triangular
prisms, `2 b₅₅ ≤ #pyramids`, and `2 q₄ ≥ #pyramids + 3 #prisms`.
In particular the row `(8,18,18,8;40)` can be assigned weight 18 without proving
that the row is unrealizable.  The weak weight 4 for `V` avoids its full local
classification when the endpoint only needs this weaker inequality.
-/

namespace Kalai5

open Set
open scoped Classical

def q55ElementaryWeight (R : Row) : ℕ :=
  if R = ⟨8, 18, 18, 8, 40⟩ then 18
  else if R = ⟨8, 19, 19, 8, 39⟩ then 4
  else if R = ⟨8, 19, 19, 8, 40⟩ then 8
  else 0

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The excess depends only on the facet row. -/
lemma IsCSPolytope5.exc_eq_faceRow {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    exc P F = (faceRow P F).J + (faceRow P F).n -
      3 * (faceRow P F).r - (faceRow P F).e := by
  have hg := hP.facet_g_eq hF h4
  simp only [Row.g, faceRow] at hg ⊢
  unfold exc
  linarith

set_option maxHeartbeats 2000000 in
/-- Three useful eight-vertex weights, obtained solely by counting. -/
theorem IsCSPolytope5.q55_elementary {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (q55ElementaryWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  by_cases h0 : faceRow P F = ⟨8, 18, 18, 8, 40⟩
  · have hn : cnt P F 0 = 8 := by
      simp only [faceRow, Row.mk.injEq] at h0
      exact h0.1
    obtain ⟨c1, c2, c3, -⟩ := hP.facet8_arith hF h4 hn
    have hb := hP.two_b55_le hF h4
    have hq := hP.q55w_eq_b55 F
    have he := hP.exc_eq_faceRow hF h4
    have hl := hP.two_q4_lb hF h4 hn (fun _ => 0)
      (fun _ _ _ _ => by positivity) (fun _ _ _ => rfl)
    simp only [Finset.sum_const_zero, add_zero] at hl
    rw [h0] at he ⊢
    norm_num [q55ElementaryWeight] at he ⊢
    simp only [faceRow, Row.mk.injEq] at h0
    omega
  by_cases h1 : faceRow P F = ⟨8, 19, 19, 8, 39⟩
  · have hn : cnt P F 0 = 8 := by
      simp only [faceRow, Row.mk.injEq] at h1
      exact h1.1
    obtain ⟨c1, c2, c3, -⟩ := hP.facet8_arith hF h4 hn
    have hb := hP.two_b55_le hF h4
    have hq := hP.q55w_eq_b55 F
    have he := hP.exc_eq_faceRow hF h4
    have hl := hP.two_q4_lb hF h4 hn (fun _ => 0)
      (fun _ _ _ _ => by positivity) (fun _ _ _ => rfl)
    simp only [Finset.sum_const_zero, add_zero] at hl
    rw [h1] at he ⊢
    norm_num [q55ElementaryWeight] at he ⊢
    simp only [faceRow, Row.mk.injEq] at h1
    omega
  by_cases h2 : faceRow P F = ⟨8, 19, 19, 8, 40⟩
  · have hn : cnt P F 0 = 8 := by
      simp only [faceRow, Row.mk.injEq] at h2
      exact h2.1
    obtain ⟨c1, c2, c3, -⟩ := hP.facet8_arith hF h4 hn
    have hb := hP.two_b55_le hF h4
    have hq := hP.q55w_eq_b55 F
    have he := hP.exc_eq_faceRow hF h4
    have hl := hP.two_q4_lb hF h4 hn (fun _ => 0)
      (fun _ _ _ _ => by positivity) (fun _ _ _ => rfl)
    simp only [Finset.sum_const_zero, add_zero] at hl
    rw [h2] at he ⊢
    norm_num [q55ElementaryWeight] at he ⊢
    simp only [faceRow, Row.mk.injEq] at h2
    omega
  · simp only [q55ElementaryWeight, h0, h1, h2, ite_false, Nat.cast_zero]
    exact hP.q55w_add_exc_nonneg F

end Kalai5
