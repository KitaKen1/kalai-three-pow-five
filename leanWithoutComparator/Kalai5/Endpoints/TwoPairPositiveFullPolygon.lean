import Kalai5.Endpoints.G2S4ABCClosure
import Kalai5.Endpoints.G2S2PolygonClosure

namespace Kalai5
open Set
open scoped Classical

namespace TwoPairPositiveProfile

def profilesFullPolygonG2S2 : List (List Row) :=
  profilesPolygonWeightG2S2.filter (fun rows => rows ∉ G2S2.polygonExcluded)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profilesFullPolygonG2S2_length : profilesFullPolygonG2S2.length = 5 := by
  simp only [profilesFullPolygonG2S2,profilesPolygonWeightG2S2,profilesPolygon,profilesNineSupport,
    profilesFullFacetCapacity,profilesContextBipyr,profilesLargeGapCapacity,
    profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_g2s4_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 4) : False := by
  have he := hP.fewFull18_positive_g2s4_last_profile hv hh h1 h6 hlt hS
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [he] at hp
  have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  rw [hS] at hb
  exact hP.g2s4_abc_false hv hp (by simpa using hb)

/-- All positive-stress counterexamples lie in the single cell (2,2). -/
theorem IsCSPolytope5.fewFull18_positive_last_cell
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (flagDataOf P).G = 2 ∧ (flagDataOf P).Gs = 2 := by
  have hc := hP.fewFull18_positive_two_cells hv hh h1 h6 hlt
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hc
  rcases hc with h | h
  · exact h
  · exact False.elim (hP.fewFull18_positive_g2s4_false hv hh h1 h6 hlt h.2)

theorem IsCSPolytope5.fewFull18_positive_full_polygon_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesFullPolygonG2S2 := by
  obtain ⟨hG,hS⟩ := hP.fewFull18_positive_last_cell hv hh h1 h6 hlt
  have hm := hP.fewFull18_positive_polygon_cell_profile_mem hv hh h1 h6 hlt
  have hn := hP.fewFull18_positive_g2s2_r0_ne hv hh h1 h6 hlt hS
  rw [hG,hS] at hm
  have hbase : positivePairRows P ∈ TwoPairPositiveProfile.profilesPolygonWeightG2S2 := by
    simpa only [TwoPairPositiveProfile.profilesPolygonWeightG2S2,List.mem_filter,
      bne_iff_ne,Bool.true_eq] using And.intro hm hn
  have hnot : positivePairRows P ∉ G2S2.polygonExcluded := by
    intro he
    have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
    have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
    rw [hS] at hb
    exact hP.g2s2_polygon_profile_false hv hp he (by simpa using hb)
  simpa only [TwoPairPositiveProfile.profilesFullPolygonG2S2,List.mem_filter,
    decide_eq_true_eq] using And.intro hbase hnot

end Kalai5
