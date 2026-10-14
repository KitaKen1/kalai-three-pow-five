import Kalai5.Endpoints.NegativeGapSupport
import Kalai5.Endpoints.QFourPairBudget
import Kalai5.Endpoints.TwoPairPositiveLowWeightRidgesProfiles

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesNegativeGap (G S : ℤ) : List (List Row) :=
  (profilesBSpecial G S).filter PrismBudget.negativeGapSupportOK

def profilesQFourPair (G S : ℤ) : List (List Row) :=
  (profilesNegativeGap G S).filter fun rows => PrismBudget.r35QFourPairBudgetOK S rows

def remainingProfilesQFourPair : List (List Row) :=
  cellsG2.flatMap fun cell => profilesQFourPair cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profileNegativeGap_counts :
    (cellsG2.map fun cell => (profilesNegativeGap cell.1 cell.2).length) = [12,13,13,4] ∧
    (cellsG2.map fun cell => (profilesQFourPair cell.1 cell.2).length) = [12,13,12,4] := by
  simp only [profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,
    profilesRidge6117,profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,
    profilesForcedPrism,profilesPairBudget,profilesEventBudget,profilesPrismBudget,
    profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesQFourPair_length : remainingProfilesQFourPair.length = 41 := by
  rw [remainingProfilesQFourPair,List.length_flatMap,profileNegativeGap_counts.2]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_negativeGap_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesNegativeGap (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_bSpecial_cell_profile_mem hv hh h1 h6 hlt,
    hP.negative_gap_pair_support hp⟩

theorem IsCSPolytope5.fewFull18_positive_qFourPair_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesQFourPair (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_negativeGap_cell_profile_mem hv hh h1 h6 hlt,
    hP.r35_single_pair_qFour_budget hp hb⟩

theorem IsCSPolytope5.fewFull18_positive_qFourPair_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesQFourPair := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_qFourPair_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5
