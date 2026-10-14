import Kalai5.Endpoints.G2S4Profiles
import Kalai5.Endpoints.G2S2R0Capacity

namespace Kalai5
open Set
open scoped Classical

namespace TwoPairPositiveProfile

def profilesPolygonWeightG2S2 : List (List Row) :=
  (profilesPolygon 2 2).filter (· != G2S2.r0Pairs)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profilesPolygonWeightG2S2_length : profilesPolygonWeightG2S2.length = 9 := by
  simp only [profilesPolygonWeightG2S2,profilesPolygon,profilesNineSupport,
    profilesFullFacetCapacity,profilesContextBipyr,profilesLargeGapCapacity,
    profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

def remainingProfilesPolygonWeight : List (List Row) :=
  profilesPolygonWeightG2S2 ++ [G2S4.bcPairs,G2S4.abcPairs]

theorem remainingProfilesPolygonWeight_length : remainingProfilesPolygonWeight.length = 11 := by
  rw [remainingProfilesPolygonWeight,List.length_append,profilesPolygonWeightG2S2_length]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_g2s2_r0_ne
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 2) :
    positivePairRows P ≠ G2S2.r0Pairs := by
  intro he
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [he] at hp
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  rw [hS] at hb
  exact hP.g2s2_r0_capacity_false hp (by simpa using hb)

theorem IsCSPolytope5.fewFull18_positive_polygon_weight_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesPolygonWeight := by
  have hc := hP.fewFull18_positive_two_cells hv hh h1 h6 hlt
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hc
  rcases hc with h | h
  · apply List.mem_append_left
    have hm := hP.fewFull18_positive_polygon_cell_profile_mem hv hh h1 h6 hlt
    have hn := hP.fewFull18_positive_g2s2_r0_ne hv hh h1 h6 hlt h.2
    rw [h.1,h.2] at hm
    simpa only [TwoPairPositiveProfile.profilesPolygonWeightG2S2,List.mem_filter,
      bne_iff_ne, Bool.true_eq] using And.intro hm hn
  · apply List.mem_append_right
    have hm := hP.fewFull18_positive_g2s4_two_profiles hv hh h1 h6 hlt h.2
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hm

end Kalai5

