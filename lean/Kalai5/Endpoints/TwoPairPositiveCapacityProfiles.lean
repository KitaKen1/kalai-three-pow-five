import Kalai5.Endpoints.Ridge6106Capacity
import Kalai5.Endpoints.LargeGapCapacity
import Kalai5.Endpoints.TwoPairPositiveNegativeGapProfiles

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesNegativeCapacity (G S : ℤ) : List (List Row) :=
  (profilesQFourPair G S).filter fun rows => PrismBudget.negativeCapacityOK S rows

def profilesRidge6106Capacity (G S : ℤ) : List (List Row) :=
  (profilesNegativeCapacity G S).filter fun rows => PrismBudget.ridge6106CapacityOK S rows

def profilesLargeGapCapacity (G S : ℤ) : List (List Row) :=
  (profilesRidge6106Capacity G S).filter fun rows => PrismBudget.largeGapCapacityOK S rows

def remainingProfilesCapacity : List (List Row) :=
  cellsG2.flatMap fun cell => profilesLargeGapCapacity cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profileCapacity_counts :
    (cellsG2.map fun cell => (profilesNegativeCapacity cell.1 cell.2).length) = [12,7,5,3] ∧
    (cellsG2.map fun cell => (profilesRidge6106Capacity cell.1 cell.2).length) = [12,5,4,3] ∧
    (cellsG2.map fun cell => (profilesLargeGapCapacity cell.1 cell.2).length) = [12,4,4,2] := by
  simp only [profilesLargeGapCapacity,profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesCapacity_length : remainingProfilesCapacity.length = 22 := by
  rw [remainingProfilesCapacity,List.length_flatMap,profileCapacity_counts.2.2]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_negativeCapacity_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesNegativeCapacity (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_qFourPair_cell_profile_mem hv hh h1 h6 hlt,
    hP.negative_gap_capacity_necessary hp hb⟩

theorem IsCSPolytope5.fewFull18_positive_ridge6106Capacity_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesRidge6106Capacity (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_negativeCapacity_cell_profile_mem hv hh h1 h6 hlt,
    hP.ridge6106_capacity_necessary hp hb⟩

theorem IsCSPolytope5.fewFull18_positive_largeGapCapacity_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesLargeGapCapacity (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_ridge6106Capacity_cell_profile_mem hv hh h1 h6 hlt,
    hP.large_gap_capacity_necessary hp hb⟩

theorem IsCSPolytope5.fewFull18_positive_capacity_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesCapacity := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_largeGapCapacity_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5
