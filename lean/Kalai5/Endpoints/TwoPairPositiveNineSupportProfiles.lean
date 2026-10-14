import Kalai5.Endpoints.FullNineSupport
import Kalai5.Endpoints.TwoPairPositiveFullFacetProfiles

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesNineSupport (G S : ℤ) : List (List Row) :=
  (profilesFullFacetCapacity G S).filter fun rows => PrismBudget.nineSupportOK S rows

def remainingProfilesNineSupport : List (List Row) :=
  cellsG2.flatMap fun cell => profilesNineSupport cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profileNineSupport_counts :
    (cellsG2.map fun cell => (profilesNineSupport cell.1 cell.2).length) = [10,3,2,1] := by
  simp only [profilesNineSupport,profilesFullFacetCapacity,profilesContextBipyr,profilesLargeGapCapacity,
    profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesNineSupport_length : remainingProfilesNineSupport.length = 16 := by
  rw [remainingProfilesNineSupport,List.length_flatMap,profileNineSupport_counts]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_nineSupport_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesNineSupport (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  have ha := (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).1
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_fullFacetCapacity_cell_profile_mem hv hh h1 h6 hlt,
    hP.nine_support_necessary hv hh ha hp hb⟩

theorem IsCSPolytope5.fewFull18_positive_nineSupport_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesNineSupport := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_nineSupport_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5

