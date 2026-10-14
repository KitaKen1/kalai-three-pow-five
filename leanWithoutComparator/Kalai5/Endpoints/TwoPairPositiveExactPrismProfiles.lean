import Kalai5.Endpoints.ExactPrismBudget
import Kalai5.Endpoints.TwoPairPositiveAntipodalProfiles

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesExactPrism (G S : ℤ) : List (List Row) :=
  (profilesForcedPrism G S).filter fun rows =>
    PrismBudget.exactPrismParityOK S rows && PrismBudget.exactEventParityOK S rows

def remainingProfilesExactPrism : List (List Row) :=
  cellsG2.flatMap fun cell => profilesExactPrism cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profileExactPrism_counts :
    (cellsG2.map fun cell => (profilesExactPrism cell.1 cell.2).length) = [19,21,16,4] := by
  simp only [profilesExactPrism,profilesForcedPrism,profilesPairBudget,profilesEventBudget,
    profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesExactPrism_length : remainingProfilesExactPrism.length = 60 := by
  rw [remainingProfilesExactPrism,List.length_flatMap,profileExactPrism_counts]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_exactPrism_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesExactPrism (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_forcedPrism_cell_profile_mem hv hh h1 h6 hlt,
    by simp only [hP.exact_prism_pair_budget_parity hp hb,
      hP.exact_event_pair_budget_parity hp hb,Bool.and_true]⟩

theorem IsCSPolytope5.fewFull18_positive_exactPrism_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesExactPrism := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_exactPrism_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5
