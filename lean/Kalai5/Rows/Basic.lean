import Kalai5.Euler.Relations
import Kalai5.Foundations

/-!
# Facts about rows of 4-polytopes

`IsRealRow R` says that `R` is the row `(f₀, f₁, f₂, f₃; f₀₃)` of a 4-dimensional polytope.

* `realRow_euler`: `n - e + p - r = 0` (Euler–Poincaré).
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-- The faces of a polytope have dimension at most its own. -/
lemma dim_le_dim_of_mem_faces {Q G : Set (E d)} (hG : G ∈ faces Q) : dim G ≤ dim Q :=
  Submodule.finrank_mono (vectorSpan_mono ℝ (face_subset hG))

/-- A polytope is its only face of its own dimension. -/
lemma fvec_dim_self {V : Finset (E d)} (hV : V.Nonempty) :
    fvec (convexHull ℝ (V : Set (E d))) (dim (convexHull ℝ (V : Set (E d)))) = 1 := by
  set Q := convexHull ℝ (V : Set (E d))
  have hQ : Q.Nonempty := hV.coe_sort.elim fun v => ⟨v, subset_convexHull ℝ _ v.2⟩
  have : {G | G ∈ faces Q ∧ dim G = dim Q} = {Q} := by
    ext G
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hG, hd⟩
      by_contra hne
      have := dim_lt_of_mem_faces_ne hG hne
      omega
    · rintro rfl; exact ⟨self_mem_faces hQ, rfl⟩
  rw [fvec, this, Set.ncard_singleton]

/-- **Euler's relation for rows of 4-polytopes.** -/
theorem realRow_euler {R : Row} (hR : IsRealRow R) : (R.n : ℤ) - R.e + R.p - R.r = 0 := by
  obtain ⟨d, Q, ⟨V, rfl⟩, hdim, rfl⟩ := hR
  have hV : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.coe_empty, convexHull_empty] at hdim
    unfold dim at hdim
    rw [vectorSpan_empty, finrank_bot] at hdim
    omega
  have h := euler_fvec hV 4 fun G hG => hdim ▸ dim_le_dim_of_mem_faces hG
  have h4 := fvec_dim_self hV
  rw [hdim] at h4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h4] at h
  simp only [rowOf]
  push_cast at h ⊢
  linarith

end Kalai5
