import Kalai5.Cube3.NoQuadrilateral
import Kalai5.Cube3.Normal
import Kalai5.Endpoints.E18refined.Closure

/-! Close the three-full-pair branch; only nine two-full-pair cells remain. -/
namespace Kalai5
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.three_pow_five_16_18_threeFull
    (hv : fvec P 0=16) (hh : fvec P 4 ≤ 18)
    (hc : 6 ≤ cnt8 (facetRows P)) : 243 ≤ (faces P).ncard := by
  by_contra hbad
  have hlt : (faces P).ncard < 243 := by omega
  obtain ⟨x,_,hrange,C,hno⟩ := Cube3.IsCSPolytope5.cube3_normal hP hv hh hc hlt
  exact C.no_three_full_configuration hP hrange hh hno

theorem IsCSPolytope5.fewFull18_residual_two
    (hv : fvec P 0=16) (hh : fvec P 4=18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    cnt8 (facetRows P)=4 ∧
      ((flagDataOf P).G,(flagDataOf P).Gs) ∈ E18refined.remainingCells 2 := by
  rcases hP.fewFull18_residual_refined hv hh h1 h6 hlt with h | h
  · exact h
  · exact ((not_le_of_gt hlt) (hP.three_pow_five_16_18_threeFull hv hh.le h.1.ge)).elim

end Kalai5
