import Kalai5.Endpoints.SinglePairBudget
import Kalai5.Endpoints.TwoPairPositiveExactPrismProfiles

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesSingleSupport (G S : ℤ) : List (List Row) :=
  (profilesExactPrism G S).filter fun rows =>
    PrismBudget.singleSupportOK PrismBudget.jRow PrismBudget.bipyrFreeRows rows &&
      PrismBudget.singleSupportOK r35Row PrismBudget.specialFreeRows rows

def profilesUniqueBudget (G S : ℤ) : List (List Row) :=
  (profilesSingleSupport G S).filter fun rows => PrismBudget.r35PairBudgetOK S rows

def remainingProfilesUniqueBudget : List (List Row) :=
  cellsG2.flatMap fun cell => profilesUniqueBudget cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profileSupport_uniqueBudget_counts :
    (cellsG2.map fun cell => (profilesSingleSupport cell.1 cell.2).length) = [17,19,16,4] ∧
    (cellsG2.map fun cell => (profilesUniqueBudget cell.1 cell.2).length) = [17,19,15,4] := by
  simp only [profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesUniqueBudget_length : remainingProfilesUniqueBudget.length = 55 := by
  rw [remainingProfilesUniqueBudget,List.length_flatMap,profileSupport_uniqueBudget_counts.2]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_singleSupport_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesSingleSupport (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_exactPrism_cell_profile_mem hv hh h1 h6 hlt,
    by simp only [hP.bipyr_single_pair_support hp,hP.r35_single_pair_support hp,Bool.and_true]⟩

theorem IsCSPolytope5.fewFull18_positive_uniqueBudget_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesUniqueBudget (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_singleSupport_cell_profile_mem hv hh h1 h6 hlt,
    hP.r35_single_pair_budget hp hb⟩

theorem IsCSPolytope5.fewFull18_positive_uniqueBudget_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesUniqueBudget := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_uniqueBudget_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5
