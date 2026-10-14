import Kalai5.Endpoints.G2S4R35
import Kalai5.Endpoints.G2S6Closure

namespace Kalai5
open Set
open scoped Classical

namespace G2S4
def bcPairs : List Row := [excRow,excRow,excRow,excRow,excRow,excRow,dRow,bRow,cRow]
def abcPairs : List Row := [excRow,excRow,excRow,excRow,excRow,aRow,aRow,bRow,cRow]
end G2S4

namespace TwoPairPositiveProfile

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem g2s4_polygon_profiles :
    profilesPolygon 2 4 = [G2S4.r35Pairs,G2S4.abcPairs,G2S4.bcPairs] := by
  simp only [profilesPolygon,profilesNineSupport,profilesFullFacetCapacity,profilesContextBipyr,profilesLargeGapCapacity,
    profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

def remainingProfilesPolygonSupport : List (List Row) :=
  profilesPolygon 2 2 ++ [G2S4.bcPairs,G2S4.abcPairs]

theorem remainingProfilesPolygonSupport_length : remainingProfilesPolygonSupport.length = 12 := by
  have hc := profilePolygon_counts
  simp only [cellsG2,List.map_cons,List.map_nil,List.cons.injEq] at hc
  rw [remainingProfilesPolygonSupport,List.length_append,hc.1]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_g2s4_two_profiles
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 4) :
    positivePairRows P = G2S4.bcPairs ∨ positivePairRows P = G2S4.abcPairs := by
  have hc := hP.fewFull18_positive_two_cells hv hh h1 h6 hlt
  have hG : (flagDataOf P).G = 2 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hc
    rcases hc with h | h <;> exact h.1
  have hm := hP.fewFull18_positive_polygon_cell_profile_mem hv hh h1 h6 hlt
  rw [hG,hS,TwoPairPositiveProfile.g2s4_polygon_profiles] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with hR | hA | hB
  · have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
    rw [hR] at hp
    have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
    rw [hS] at hb
    exact False.elim (hP.g2s4_r35_false hp (by simpa using hb))
  · exact Or.inr hA
  · exact Or.inl hB

theorem IsCSPolytope5.fewFull18_positive_polygon_support_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesPolygonSupport := by
  have hc := hP.fewFull18_positive_two_cells hv hh h1 h6 hlt
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hc
  rcases hc with h | h
  · have hm := hP.fewFull18_positive_polygon_cell_profile_mem hv hh h1 h6 hlt
    exact List.mem_append_left _ (by simpa only [h.1,h.2] using hm)
  · apply List.mem_append_right
    have hm := hP.fewFull18_positive_g2s4_two_profiles hv hh h1 h6 hlt h.2
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hm

end Kalai5
