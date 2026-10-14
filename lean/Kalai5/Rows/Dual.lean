import Kalai5.Rows.Basic
import Kalai5.Polar.Flags
import Kalai5.Pyramid.Recognition

/-!
# Duals of rows

`realRow_dual`: if `(n, e, p, r; J)` is the row of a 4-polytope, so is `(r, p, e, n; J)` (the row
of its polar, after moving the polytope to its own affine hull with `0` in the interior).
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-- Polarity reverses face numbers of a polytope with `0` in its interior. -/
lemma fvec_polarSet_eq {V : Finset (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d)))) (k : ℕ) (hk : k + 1 ≤ d) :
    fvec (polarSet (convexHull ℝ (V : Set (E d)))) (d - 1 - k) =
      fvec (convexHull ℝ (V : Set (E d))) k := by
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E d) ∈ interior (convexHull ℝ (W : Set (E d))) :=
    hW ▸ zero_mem_interior_polarSet V
  have hbip : polarSet (convexHull ℝ (W : Set (E d))) = convexHull ℝ (V : Set (E d)) := by
    rw [← hW]
    exact polarSet_polarSet (convex_convexHull ℝ _) (Set.Finite.isClosed_convexHull ℝ V.finite_toSet)
      (interior_subset h0)
  have h1 := fvec_le_fvec_polarSet h0 k hk
  have h2 := fvec_le_fvec_polarSet h0W (d - 1 - k) (by omega)
  rw [hbip, show d - 1 - (d - 1 - k) = k by omega, ← hW] at h2
  omega

/-- Polarity reverses flag numbers of a polytope with `0` in its interior. -/
lemma flag2_polarSet_eq {V : Finset (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d)))) (i j : ℕ) (hi : i + 1 ≤ d)
    (hj : j + 1 ≤ d) :
    flag2 (polarSet (convexHull ℝ (V : Set (E d)))) (d - 1 - j) (d - 1 - i) =
      flag2 (convexHull ℝ (V : Set (E d))) i j := by
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E d) ∈ interior (convexHull ℝ (W : Set (E d))) :=
    hW ▸ zero_mem_interior_polarSet V
  have hbip : polarSet (convexHull ℝ (W : Set (E d))) = convexHull ℝ (V : Set (E d)) := by
    rw [← hW]
    exact polarSet_polarSet (convex_convexHull ℝ _) (Set.Finite.isClosed_convexHull ℝ V.finite_toSet)
      (interior_subset h0)
  have h1 := flag2_le_flag2_polarSet h0 i j hj
  have h2 := flag2_le_flag2_polarSet h0W (d - 1 - j) (d - 1 - i) (by omega)
  rw [hbip, show d - 1 - (d - 1 - i) = i by omega, show d - 1 - (d - 1 - j) = j by omega,
    ← hW] at h2
  omega

/-- The dual row, in the standard space of the right dimension. -/
lemma realRow_dual_of_interior {k : ℕ} (hk : k = 4) {V : Finset (E k)}
    (h0 : (0 : E k) ∈ interior (convexHull ℝ (V : Set (E k)))) :
    IsRealRow ⟨fvec (convexHull ℝ (V : Set (E k))) 3, fvec (convexHull ℝ (V : Set (E k))) 2,
      fvec (convexHull ℝ (V : Set (E k))) 1, fvec (convexHull ℝ (V : Set (E k))) 0,
      flag2 (convexHull ℝ (V : Set (E k))) 0 3⟩ := by
  subst hk
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E 4) ∈ interior (convexHull ℝ (W : Set (E 4))) :=
    hW ▸ zero_mem_interior_polarSet V
  refine ⟨4, convexHull ℝ (W : Set (E 4)), ⟨W, rfl⟩,
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0W⟩, ?_⟩
  have e0 := fvec_polarSet_eq h0 3 (by norm_num)
  have e1 := fvec_polarSet_eq h0 2 (by norm_num)
  have e2 := fvec_polarSet_eq h0 1 (by norm_num)
  have e3 := fvec_polarSet_eq h0 0 (by norm_num)
  have eJ := flag2_polarSet_eq h0 0 3 (by norm_num) (by norm_num)
  rw [hW] at e0 e1 e2 e3 eJ
  norm_num at e0 e1 e2 e3 eJ
  simp only [rowOf, e0, e1, e2, e3, eJ]

/-- **The dual of a row of a 4-polytope is a row of a 4-polytope.** -/
theorem realRow_dual {R : Row} (hR : IsRealRow R) : IsRealRow ⟨R.r, R.p, R.e, R.n, R.J⟩ := by
  obtain ⟨d, Q, ⟨V, hQ⟩, hdim, rfl⟩ := hR
  have hne : Q.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hdim
    unfold dim at hdim
    rw [vectorSpan_empty, finrank_bot] at hdim
    omega
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hQ hne
  have := realRow_dual_of_interior hdim h0
  simp only [rowOf, ← hV', ← fvec_affEmb hp, ← flag2_affEmb hp] at this ⊢
  exact this

end Kalai5
