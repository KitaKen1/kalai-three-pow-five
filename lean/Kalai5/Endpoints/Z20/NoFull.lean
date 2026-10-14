import Kalai5.Endpoints.E20k.Closure
import Kalai5.Endpoints.SixteenNoFull

/-!
# Endpoint `(16,20)` without full facets (Z20)

`IsCSPolytope5.three_pow_five_16_20_noFull`: a centrally symmetric 5-polytope with sixteen
vertices, twenty facets and no facet with eight vertices has at least `243` nonempty faces.
Every facet row has `n ≤ 7` (`nF = 7`); the quadrilateral-link inequality
`9 #Y + 4 #E ≤ 4A + 2(f₀₂₄ - 3 f₂₄)` (`IsCSPolytope5.quadLink`) enters the certificates of
`E20k.closure20`.
-/

namespace Kalai5

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **Sixteen vertices, twenty facets, no full facet**: at least `243` faces. -/
theorem IsCSPolytope5.three_pow_five_16_20_noFull (hv : fvec P 0 = 16) (hh : fvec P 4 = 20)
    (hn : ∀ R ∈ facetRows P, R.n ≤ 7) : 243 ≤ (faces P).ncard := by
  by_contra hlt
  push_neg at hlt
  have hD := hP.flagData_valid
  have htot : (flagDataOf P).total < 243 := by
    have h := hP.faces_ncard
    change _ = (flagDataOf P).total at h
    rw [← h]
    exact hlt
  have ht : (flagDataOf P).t ≤ 118 := by
    by_contra h
    exact absurd (FlagData.total_ge_of_t_gt hD (by omega)) (by omega)
  have ht' : ((flagDataOf P).t : ℤ) ≤ 118 := by exact_mod_cast ht
  exact E20k.closure20 (hP.ctx16k (nS := 10) hv hh (by norm_num) hn) hP.quadLink ht'

end cs

end Kalai5
