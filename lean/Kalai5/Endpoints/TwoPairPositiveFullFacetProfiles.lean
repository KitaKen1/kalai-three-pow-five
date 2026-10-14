import Kalai5.Endpoints.FullFacetCapacity
import Kalai5.Endpoints.TwoPairPositiveContextProfiles

namespace Kalai5
open scoped Classical

namespace PrismBudget

def fullFacetCapacityOK (rows : List Row) : Bool :=
  rows.all fun R => decide (R.n ≠ 8 ∨ R.r ≤ 9)

end PrismBudget

namespace TwoPairPositiveProfile

def profilesFullFacetCapacity (G S : ℤ) : List (List Row) :=
  (profilesContextBipyr G S).filter PrismBudget.fullFacetCapacityOK

def remainingProfilesFullFacetCapacity : List (List Row) :=
  cellsG2.flatMap fun cell => profilesFullFacetCapacity cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profileFullFacetCapacity_counts :
    (cellsG2.map fun cell => (profilesFullFacetCapacity cell.1 cell.2).length) = [11,4,2,2] := by
  simp only [profilesFullFacetCapacity,profilesContextBipyr,profilesLargeGapCapacity,
    profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesFullFacetCapacity_length : remainingProfilesFullFacetCapacity.length = 19 := by
  rw [remainingProfilesFullFacetCapacity,List.length_flatMap,profileFullFacetCapacity_counts]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.full_facet_capacity_necessary
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (ha : cnt8 (facetRows P) = 4)
    {rows : List Row} (hp : (facetRows P).Perm (rows ++ rows)) :
    PrismBudget.fullFacetCapacityOK rows = true := by
  apply List.all_eq_true.2
  intro R hRm
  apply decide_eq_true
  by_cases hn : R.n = 8
  · apply Or.inr
    obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _ hRm))
    have hF8 : cnt P F 0 = 8 := by change (faceRow P F).n = 8; rw [hR,hn]
    have hc := hP.full_facet_nine_ridges_of_four_full hv hh ha hF h4 hF8
    change (faceRow P F).r ≤ 9 at hc
    rwa [hR] at hc
  · exact Or.inl hn

theorem IsCSPolytope5.fewFull18_positive_fullFacetCapacity_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesFullFacetCapacity (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have ha := (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).1
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_contextBipyr_cell_profile_mem hv hh h1 h6 hlt,
    hP.full_facet_capacity_necessary hv hh ha hp⟩

theorem IsCSPolytope5.fewFull18_positive_fullFacetCapacity_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesFullFacetCapacity := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_fullFacetCapacity_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5

