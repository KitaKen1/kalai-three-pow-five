import Kalai5.Endpoints.PairBudgetParity
import Kalai5.Endpoints.WeightForcedPrism
import Kalai5.Endpoints.TwoPairPositivePrismBudgetProfiles

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesPairBudget (G S : ℤ) : List (List Row) :=
  (profilesEventBudget G S).filter fun rows =>
    PrismBudget.pairParityOK S rows && PrismBudget.pairEventParityOK S rows

def profilesForcedPrism (G S : ℤ) : List (List Row) :=
  (profilesPairBudget G S).filter fun rows =>
    decide (((rows.map q55ForcedPrismRowWeight).sum : ℤ) ≤ 78 - 3 * S)

def remainingProfilesForcedPrism : List (List Row) :=
  cellsG2.flatMap fun cell => profilesForcedPrism cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profilePairBudget_forcedPrism_counts :
    (cellsG2.map fun cell => (profilesPairBudget cell.1 cell.2).length) = [25,27,16,4] ∧
    (cellsG2.map fun cell => (profilesForcedPrism cell.1 cell.2).length) = [24,25,16,4] := by
  simp only [profilesForcedPrism,profilesPairBudget,profilesEventBudget,
    profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesForcedPrism_length : remainingProfilesForcedPrism.length = 69 := by
  rw [remainingProfilesForcedPrism,List.length_flatMap,profilePairBudget_forcedPrism_counts.2]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_pairBudget_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesPairBudget (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_eventBudget_cell_profile_mem hv hh h1 h6 hlt,
    by simp only [hP.prism_pair_budget_parity hp hb,hP.event_pair_budget_parity hp hb,Bool.and_true]⟩

theorem IsCSPolytope5.fewFull18_positive_forcedPrism_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesForcedPrism (flagDataOf P).G (flagDataOf P).Gs := by
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_pairBudget_cell_profile_mem hv hh h1 h6 hlt,
    decide_eq_true (hP.fewFull18_positive_forcedPrism_pair_budget hv hh h1 h6 hlt)⟩

theorem IsCSPolytope5.fewFull18_positive_forcedPrism_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesForcedPrism := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_forcedPrism_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5
