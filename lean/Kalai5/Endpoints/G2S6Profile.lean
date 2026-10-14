import Kalai5.Endpoints.G2S6Weights
import Kalai5.Endpoints.TwoPairPositivePolygonProfiles

namespace Kalai5
open Set
open scoped Classical

namespace TwoPairPositiveProfile

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem g2s6_polygon_profile : profilesPolygon 2 6 = [G2S6.pairs] := by
  simp only [profilesPolygon,profilesNineSupport,profilesFullFacetCapacity,profilesContextBipyr,profilesLargeGapCapacity,
    profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_g2s6_profile
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 6) :
    (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs) := by
  have hc := hP.fewFull18_positive_polygon_three_cells hv hh h1 h6 hlt
  have hG : (flagDataOf P).G = 2 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hc
    rcases hc with h | h | h <;> exact h.1
  have hm := hP.fewFull18_positive_polygon_cell_profile_mem hv hh h1 h6 hlt
  rw [hG,hS,TwoPairPositiveProfile.g2s6_polygon_profile,List.mem_singleton] at hm
  simpa only [hm] using hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt

theorem IsCSPolytope5.fewFull18_positive_g2s6_weight_eq
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 6)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F = G2S6.rowWeight (faceRow P F) := by
  have hp := hP.fewFull18_positive_g2s6_profile hv hh h1 h6 hlt hS
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  rw [hS] at hb
  exact hP.g2s6_weight_eq hp (by simpa using hb) hF h4

end Kalai5
