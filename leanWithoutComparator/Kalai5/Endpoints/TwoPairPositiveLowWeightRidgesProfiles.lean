import Kalai5.Endpoints.Ridge6117Budget
import Kalai5.Endpoints.WeightQFour
import Kalai5.Endpoints.BSupportBudget
import Kalai5.Endpoints.TwoPairPositiveSupportProfiles

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesRidge6117 (G S : ℤ) : List (List Row) :=
  (profilesUniqueBudget G S).filter fun rows => PrismBudget.ridge6117ParityOK S rows

def profilesQFour (G S : ℤ) : List (List Row) :=
  (profilesRidge6117 G S).filter fun rows =>
    decide (((rows.map q55QFourRowWeight).sum : ℤ) ≤ 78 - 3 * S)

def profilesBSpecial (G S : ℤ) : List (List Row) :=
  (profilesQFour G S).filter fun rows => PrismBudget.bSupportOK S rows

def remainingProfilesBSpecial : List (List Row) :=
  cellsG2.flatMap fun cell => profilesBSpecial cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profileLowWeightRidges_counts :
    (cellsG2.map fun cell => (profilesRidge6117 cell.1 cell.2).length) = [17,18,14,4] ∧
    (cellsG2.map fun cell => (profilesQFour cell.1 cell.2).length) = [17,17,14,4] ∧
    (cellsG2.map fun cell => (profilesBSpecial cell.1 cell.2).length) = [17,17,13,4] := by
  simp only [profilesBSpecial,profilesQFour,profilesRidge6117,profilesUniqueBudget,
    profilesSingleSupport,profilesExactPrism,profilesForcedPrism,profilesPairBudget,
    profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesBSpecial_length : remainingProfilesBSpecial.length = 51 := by
  rw [remainingProfilesBSpecial,List.length_flatMap,profileLowWeightRidges_counts.2.2]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_ridge6117_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesRidge6117 (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_uniqueBudget_cell_profile_mem hv hh h1 h6 hlt,
    hP.ridge6117_pair_budget_parity hp hb⟩

theorem IsCSPolytope5.fewFull18_positive_qFour_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesQFour (flagDataOf P).G (flagDataOf P).Gs := by
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_ridge6117_cell_profile_mem hv hh h1 h6 hlt,
    decide_eq_true (hP.fewFull18_positive_qFour_pair_budget hv hh h1 h6 hlt)⟩

theorem IsCSPolytope5.fewFull18_positive_bSpecial_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesBSpecial (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_qFour_cell_profile_mem hv hh h1 h6 hlt,
    hP.b_single_support_budget hp hb⟩

theorem IsCSPolytope5.fewFull18_positive_bSpecial_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesBSpecial := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_bSpecial_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5
