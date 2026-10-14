import Kalai5.Rows.Dual
import Kalai5.Rows.Degree

/-!
# Nonnegative polygon excess and its dual for every real four-dimensional row

Every polygon has at least three vertices. Combining this with the summed
Euler relations of the vertex figures gives `e + 3r ≤ J + n`. Applying the
same statement to the dual gives `p + 3n ≤ J + r`.
-/

namespace Kalai5
open Set
open scoped Classical

/-- The local excess bounds are valid for arbitrary real rows, without central symmetry. -/
theorem realRow_polygon_excess {R : Row} (hR : IsRealRow R) :
    R.e + 3 * R.r ≤ R.J + R.n := by
  have hEuler := realRow_euler hR
  obtain ⟨d, Q, ⟨V, rfl⟩, hdim, rfl⟩ := hR
  simp only [rowOf] at hEuler ⊢
  have hvertex : ∀ v ∈ (kfaces_finite_conv V 0).toFinset,
      (upIn (convexHull ℝ (V : Set (E d))) v 1 : ℤ) -
        upIn (convexHull ℝ (V : Set (E d))) v 2 +
        upIn (convexHull ℝ (V : Set (E d))) v 3 = 2 := by
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    exact vertex_up_dim_four rfl hdim hv.1 hv.2
  have hs := Finset.sum_congr rfl hvertex
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum,
    Finset.sum_const, nsmul_eq_mul, card_kfaces_eq_fvec,
    ← flag2_eq_sum_upIn_conv, ← flag2_eq_sum_upIn_conv, ← flag2_eq_sum_upIn_conv,
    flag2_zero_one] at hs
  have hpoly : 3 * fvec (convexHull ℝ (V : Set (E d))) 2 ≤
      flag2 (convexHull ℝ (V : Set (E d))) 0 2 := by
    rw [flag2_eq_sum_cnt_conv, ← card_kfaces_eq_fvec, mul_comm,
      ← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro F hF
    rw [Set.Finite.mem_toFinset] at hF
    exact three_le_cnt_zero_of_dim_two hF.1 hF.2
  push_cast at hs
  omega

/-- The dual polygon-excess bound. -/
theorem realRow_dual_polygon_excess {R : Row} (hR : IsRealRow R) :
    R.p + 3 * R.n ≤ R.J + R.r := realRow_polygon_excess (realRow_dual hR)

end Kalai5
