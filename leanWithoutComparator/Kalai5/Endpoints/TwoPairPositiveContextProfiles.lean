import Kalai5.Endpoints.CContextSupport
import Kalai5.Endpoints.TwoPairPositiveCapacityProfiles

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesContextBipyr (G S : ℤ) : List (List Row) :=
  (profilesLargeGapCapacity G S).filter fun rows => PrismBudget.contextBipyrCapacityOK S rows

def remainingProfilesContextBipyr : List (List Row) :=
  cellsG2.flatMap fun cell => profilesContextBipyr cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profileContextBipyr_counts :
    (cellsG2.map fun cell => (profilesContextBipyr cell.1 cell.2).length) = [12,4,2,2] := by
  simp only [profilesContextBipyr,profilesLargeGapCapacity,profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesContextBipyr_length : remainingProfilesContextBipyr.length = 20 := by
  rw [remainingProfilesContextBipyr,List.length_flatMap,profileContextBipyr_counts]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_contextBipyr_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesContextBipyr (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_largeGapCapacity_cell_profile_mem hv hh h1 h6 hlt,
    hP.context_bipyr_capacity_necessary hp hb⟩

theorem IsCSPolytope5.fewFull18_positive_contextBipyr_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesContextBipyr := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_contextBipyr_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5

