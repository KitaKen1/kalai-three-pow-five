import Kalai5.Endpoints.EventBudget
import Kalai5.Endpoints.G4S2Closure

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesQ3 (G S : ℤ) : List (List Row) :=
  (profilesV12 G S).filter fun rows => decide (((rows.map q55QThreeRowWeight).sum : ℤ) ≤ 78 - 3 * S)

def profilesPrismBudget (G S : ℤ) : List (List Row) :=
  (profilesQ3 G S).filter (PrismBudget.parityOK S)

def profilesEventBudget (G S : ℤ) : List (List Row) :=
  (profilesPrismBudget G S).filter (PrismBudget.eventParityOK S)

def remainingProfilesEventBudget : List (List Row) :=
  cellsG2.flatMap fun cell => profilesEventBudget cell.1 cell.2

def remainingProfilesPrismBudget : List (List Row) :=
  cellsG2.flatMap fun cell => profilesPrismBudget cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profileQ3_prismBudget_counts :
    (cellsG2.map fun cell => (profilesQ3 cell.1 cell.2).length) = [38,48,29,10] ∧
    (cellsG2.map fun cell => (profilesPrismBudget cell.1 cell.2).length) = [37,41,26,6] ∧
    (cellsG2.map fun cell => (profilesEventBudget cell.1 cell.2).length) = [30,29,22,4] := by
  simp only [profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesPrismBudget_length : remainingProfilesPrismBudget.length = 110 := by
  rw [remainingProfilesPrismBudget,List.length_flatMap,profileQ3_prismBudget_counts.2.1]
  rfl

theorem remainingProfilesEventBudget_length : remainingProfilesEventBudget.length = 85 := by
  rw [remainingProfilesEventBudget,List.length_flatMap,profileQ3_prismBudget_counts.2.2]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_q3_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesQ3 (flagDataOf P).G (flagDataOf P).Gs := by
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_v12_cell_profile_mem hv hh h1 h6 hlt,
    decide_eq_true (hP.fewFull18_positive_qThree_pair_budget hv hh h1 h6 hlt)⟩

theorem IsCSPolytope5.fewFull18_positive_prismBudget_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesPrismBudget (flagDataOf P).G (flagDataOf P).Gs := by
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_q3_cell_profile_mem hv hh h1 h6 hlt,
    hP.prism_budget_parity (hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt)
      (hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt)⟩

/-- The geometric Q weight and prism parity leave exactly 110 pair profiles. -/
theorem IsCSPolytope5.fewFull18_positive_prismBudget_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesPrismBudget := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_prismBudget_cell_profile_mem hv hh h1 h6 hlt⟩

theorem IsCSPolytope5.fewFull18_positive_eventBudget_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesEventBudget (flagDataOf P).G (flagDataOf P).Gs := by
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_prismBudget_cell_profile_mem hv hh h1 h6 hlt,
    hP.event_budget_parity (hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt)
      (hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt)⟩

/-- Both parity filters together leave the kernel-counted list of 85 profiles. -/
theorem IsCSPolytope5.fewFull18_positive_eventBudget_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesEventBudget := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_eventBudget_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5
