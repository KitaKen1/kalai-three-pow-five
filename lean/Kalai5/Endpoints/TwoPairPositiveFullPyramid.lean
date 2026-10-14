import Kalai5.Endpoints.G2S2R35Closure

namespace Kalai5
open Set
open scoped Classical
namespace TwoPairPositiveProfile

def profilesFullPyramidG2S2 : List (List Row) :=
  profilesNineTetraG2S2.filter (fun rows => rows ∉ G2S2.r35Excluded)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profilesFullPyramidG2S2_length : profilesFullPyramidG2S2.length = 1 := by
  simp only [profilesFullPyramidG2S2,profilesNineTetraG2S2,profilesFullPolygonG2S2,profilesPolygonWeightG2S2,profilesPolygon,profilesNineSupport,
    profilesFullFacetCapacity,profilesContextBipyr,profilesLargeGapCapacity,
    profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

end TwoPairPositiveProfile
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Only original profile 29 survives the full-pyramid and R35 supply obstruction. -/
theorem IsCSPolytope5.fewFull18_positive_full_pyramid_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesFullPyramidG2S2 := by
  have hm := hP.fewFull18_positive_nine_tetra_profile_mem hv hh h1 h6 hlt
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hc := (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).1
  have hn : positivePairRows P ∉ G2S2.r35Excluded := fun he => hP.g2s2_r35_profiles_false hv hh hc hp he
  simpa only [TwoPairPositiveProfile.profilesFullPyramidG2S2,List.mem_filter,
    decide_eq_true_eq] using And.intro hm hn

end Kalai5
