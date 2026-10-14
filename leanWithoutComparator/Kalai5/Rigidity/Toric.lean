import Kalai5.Rigidity.Basic
import Kalai5.Small.Model

/-!
# The centrally symmetric toric bound `G ≥ 0` from Whiteley's rigidity theorem

`WhiteleyCS P` is the conclusion of Whiteley's theorem (Sanyal–Werner–Ziegler, Thm 2.3) for an
antipodally symmetric triangulation of the 2-skeleton of `P` without new vertices: there is a set
`B` of bars between vertices, closed under `x ↦ -x` without fixed bars, with
`|B| = f₁ + f₀₂ - 3f₂` (each `k`-gon gets `k - 3` diagonals; the same count holds inside every
facet, since the triangulation restricts to the facets), whose framework is infinitesimally
rigid.  From it, `card_le_of_infRigid_symm` gives `5 f₀ ≤ |B| + 10`, i.e. `G ≥ 0`
(`IsCSPolytope5.G_nonneg_of_whiteley`).
-/

namespace Kalai5

open Set

open Classical in
/-- The conclusion of Whiteley's rigidity theorem for an antipodally symmetric triangulation of
the 2-skeleton of `P` (Sanyal–Werner–Ziegler, Thm 2.3; Whiteley 1984). -/
def WhiteleyCS (P : Set E5) : Prop :=
  ∃ B : Finset (Sym2 E5),
    (∀ b ∈ B, ∀ p ∈ b, p ∈ P.extremePoints ℝ) ∧
    (∀ b ∈ B, b.map Neg.neg ∈ B ∧ b.map Neg.neg ≠ b) ∧
    (B.card : ℤ) = fvec P 1 + flag2 P 0 2 - 3 * fvec P 2 ∧
    (∀ F ∈ faces P, dim F = 4 → ((B.filter fun b => ∀ p ∈ b, p ∈ F).card : ℤ) =
      cnt P F 1 + incid P F 0 2 - 3 * cnt P F 2) ∧
    IsInfRigid (P.extremePoints ℝ) (B : Set (Sym2 E5))

/-- The vertices of a polytope with `0` in its interior span the space. -/
lemma span_extremePoints_eq_top {V : Finset E5}
    (h0 : (0 : E5) ∈ interior (convexHull ℝ (V : Set E5))) :
    Submodule.span ℝ ((convexHull ℝ (V : Set E5)).extremePoints ℝ) = ⊤ := by
  set S := (convexHull ℝ (V : Set E5)).extremePoints ℝ
  have hsub : convexHull ℝ (V : Set E5) ⊆ Submodule.span ℝ S := by
    rw [← convexHull_extremePoints_eq V]
    exact convexHull_min Submodule.subset_span (Submodule.span ℝ S).convex
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h0)
  rw [Submodule.eq_top_iff']
  intro y
  by_cases hy : y = 0
  · rw [hy]; exact Submodule.zero_mem _
  · have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy
    set t : ℝ := r / (2 * ‖y‖)
    have ht : 0 < t := by positivity
    have hmem : t • y ∈ convexHull ℝ (V : Set E5) := by
      apply hball
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have : t * ‖y‖ = r / 2 := by
        simp only [t]; field_simp
      rw [this]; linarith
    have := Submodule.smul_mem _ t⁻¹ (hsub hmem)
    rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **`G ≥ 0` from Whiteley's theorem.** -/
theorem IsCSPolytope5.G_nonneg_of_whiteley (hW : WhiteleyCS P) : 0 ≤ (flagDataOf P).G := by
  classical
  obtain ⟨B, -, hBs, hBcard, -, hrig⟩ := hW
  obtain ⟨V, hV⟩ := hP.polytope
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hXcard : X.card = fvec P 0 := by
    have h1 := fvec_zero_eq V
    rw [Set.ncard_eq_toFinset_card _ (extremePoints_finite V)] at h1
    rw [hV, hXdef, h1]
  have hXs : ∀ x ∈ X, -x ∈ X := by
    intro x hx
    rw [← Finset.mem_coe, hXcoe] at hx ⊢
    exact neg_mem_extremePoints hP.symm hx
  have hX0 : (0 : E5) ∉ X := by
    rw [← Finset.mem_coe, hXcoe]
    exact hP.zero_not_mem_extremePoints
  have hspan : Submodule.span ℝ (X : Set E5) = ⊤ := by
    rw [hXcoe, hV]
    exact span_extremePoints_eq_top (hV ▸ hP.zero_mem_interior)
  have key := card_le_of_infRigid_symm hXs hX0 hspan (fun b hb => (hBs b hb).1)
    (fun b hb => (hBs b hb).2) (by rw [hXcoe]; exact hrig)
  rw [hXcard] at key
  simp only [FlagData.G, flagDataOf]
  have key' : (5 : ℤ) * fvec P 0 ≤ B.card + 10 := by exact_mod_cast key
  rw [hBcard] at key'
  linarith

end cs

end Kalai5
