import Kalai5.Rows.Degree
import Kalai5.Rows.Basic
import Kalai5.Polar.General

/-!
# A shorter target for the low-height branch

Ten vertices in dimension three force seven facets by Euler and minimum
vertex degree. Central-symmetry parity is unnecessary: 3 * 7 = 21 already
contradicts the eighteen-facet endpoint. The auxiliary geometric realization
must still supply the hypotheses; this is not a closure of the (5,1,1,1) case.
-/

namespace Kalai5.Cube3

open Set

/-- No classification of three-polytopes, and no parity assumption, is needed. -/
theorem seven_facets_of_ten_vertices {d : ℕ} (V : Finset (E d)) (hV : V.Nonempty)
    (h3 : dim (convexHull ℝ (V : Set (E d))) = 3)
    (h10 : 10 ≤ fvec (convexHull ℝ (V : Set (E d))) 0) :
    7 ≤ fvec (convexHull ℝ (V : Set (E d))) 2 := by
  have hdeg := three_fvec_zero_le V h3
  have he := euler_fvec hV 3 fun G hG => h3 ▸ dim_le_dim_of_mem_faces hG
  have htop := fvec_dim_self hV
  rw [h3] at htop
  norm_num [Finset.sum_range_succ, htop] at he
  omega

/-- The dual form needed for the auxiliary body. -/
theorem seven_polar_vertices_of_ten_vertices (V : Finset (E 3))
    (h0 : (0 : E 3) ∈ interior (convexHull ℝ (V : Set (E 3))))
    (h10 : 10 ≤ fvec (convexHull ℝ (V : Set (E 3))) 0) :
    7 ≤ fvec (polarSet (convexHull ℝ (V : Set (E 3)))) 0 := by
  have hV : V.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.1 h
    simp [he] at h0
  have h3 : dim (convexHull ℝ (V : Set (E 3))) = 3 :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have h := seven_facets_of_ten_vertices V hV h3 h10
  rwa [fvec_polarSet_zero h0 (by norm_num)]

end Kalai5.Cube3
