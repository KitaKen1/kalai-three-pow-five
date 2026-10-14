import Kalai5.Endpoints.RidgePolygonCapacity
import Kalai5.Endpoints.TwoPairPositiveNineSupportProfiles

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesPolygon (G S : ℤ) : List (List Row) :=
  (profilesNineSupport G S).filter fun rows => PrismBudget.ridgePolygonOK S rows

def remainingProfilesPolygon : List (List Row) :=
  cellsG2.flatMap fun cell => profilesPolygon cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profilePolygon_counts :
    (cellsG2.map fun cell => (profilesPolygon cell.1 cell.2).length) = [10,3,1,0] := by
  simp only [profilesPolygon,profilesNineSupport,profilesFullFacetCapacity,profilesContextBipyr,profilesLargeGapCapacity,
    profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesPolygon_length : remainingProfilesPolygon.length = 14 := by
  rw [remainingProfilesPolygon,List.length_flatMap,profilePolygon_counts]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_polygon_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesPolygon (flagDataOf P).G (flagDataOf P).Gs := by
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_nineSupport_cell_profile_mem hv hh h1 h6 hlt,
    hP.ridge_polygon_capacity_necessary hp hb⟩

theorem IsCSPolytope5.fewFull18_positive_polygon_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesPolygon := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_polygon_cell_profile_mem hv hh h1 h6 hlt⟩

/-- The entire (G,Gs)=(2,8) cell is now excluded. -/
theorem IsCSPolytope5.fewFull18_positive_polygon_three_cells
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    ((flagDataOf P).G,(flagDataOf P).Gs) ∈ ([(2,2),(2,4),(2,6)] : List (ℤ × ℤ)) := by
  have hm := hP.fewFull18_positive_polygon_cell_profile_mem hv hh h1 h6 hlt
  have hc := hP.fewFull18_positive_four_cells hv hh h1 h6 hlt
  have hz : TwoPairPositiveProfile.profilesPolygon 2 8 = [] := by
    have hcounts := TwoPairPositiveProfile.profilePolygon_counts
    simp only [TwoPairPositiveProfile.cellsG2,List.map_cons,List.map_nil,List.cons.injEq] at hcounts
    exact List.length_eq_zero_iff.1 hcounts.2.2.2.1
  simp only [TwoPairPositiveProfile.cellsG2,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hc
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · rw [h.1,h.2,hz] at hm
    exact False.elim (List.not_mem_nil hm)

end Kalai5
