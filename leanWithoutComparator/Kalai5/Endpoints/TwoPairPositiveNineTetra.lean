import Kalai5.Endpoints.G2S2NineR0
import Kalai5.Endpoints.G2S2NineQClosure

namespace Kalai5
open Set
open scoped Classical
namespace TwoPairPositiveProfile

def profilesNineTetraG2S2 : List (List Row) :=
  profilesFullPolygonG2S2.filter (fun rows => rows != G2S2.nineR0Pairs && rows != G2S2.nineQPairs)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profilesNineTetraG2S2_length : profilesNineTetraG2S2.length = 3 := by
  simp only [profilesNineTetraG2S2,profilesFullPolygonG2S2,profilesPolygonWeightG2S2,profilesPolygon,profilesNineSupport,
    profilesFullFacetCapacity,profilesContextBipyr,profilesLargeGapCapacity,
    profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

end TwoPairPositiveProfile
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_nine_tetra_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesNineTetraG2S2 := by
  have hm := hP.fewFull18_positive_full_polygon_profile_mem hv hh h1 h6 hlt
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hc := (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).1
  have hS := (hP.fewFull18_positive_last_cell hv hh h1 h6 hlt).2
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  rw [hS] at hb
  have hR : positivePairRows P ≠ G2S2.nineR0Pairs := by
    intro he
    rw [he] at hp
    exact hP.g2s2_nine_r0_false hv hh hc hp
  have hQ : positivePairRows P ≠ G2S2.nineQPairs := by
    intro he
    rw [he] at hp
    exact hP.g2s2_nine_q_false hv hh hc hp (by simpa using hb)
  simpa only [TwoPairPositiveProfile.profilesNineTetraG2S2,List.mem_filter,
    Bool.and_eq_true,bne_iff_ne,Bool.true_eq] using And.intro hm (And.intro hR hQ)

end Kalai5
