import Kalai5.Endpoints.TwoPairPositiveFullPyramid

namespace Kalai5
open Set
open scoped Classical
namespace G2S2
def lastPairs : List Row := [excRow,excRow,excRow,excRow,excRow,excRow,d36Row,G2S4.bRow,G2S4.bRow]
end G2S2
namespace TwoPairPositiveProfile
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profilesFullPyramidG2S2_eq_singleton : profilesFullPyramidG2S2 = [G2S2.lastPairs] := by
  simp only [profilesFullPyramidG2S2,profilesNineTetraG2S2,profilesFullPolygonG2S2,profilesPolygonWeightG2S2,profilesPolygon,profilesNineSupport,
    profilesFullFacetCapacity,profilesContextBipyr,profilesLargeGapCapacity,
    profilesRidge6106Capacity,profilesNegativeCapacity,
    profilesQFourPair,profilesNegativeGap,profilesBSpecial,profilesQFour,profilesRidge6117,
    profilesUniqueBudget,profilesSingleSupport,profilesExactPrism,profilesForcedPrism,
    profilesPairBudget,profilesEventBudget,profilesPrismBudget,profilesQ3,profilesV12,profiles_guarded]
  decide +kernel
end TwoPairPositiveProfile
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_last_pairs
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) : positivePairRows P = G2S2.lastPairs := by
  have hm := hP.fewFull18_positive_full_pyramid_profile_mem hv hh h1 h6 hlt
  rwa [TwoPairPositiveProfile.profilesFullPyramidG2S2_eq_singleton,List.mem_singleton] at hm

theorem IsCSPolytope5.g2s2_last_row_cases
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    faceRow P F = excRow ∨ faceRow P F = G2S2.d36Row ∨ faceRow P F = G2S4.bRow := by
  have hm := hP.faceRow_mem_pair_rows hp hF h4
  simpa only [G2S2.lastPairs,List.mem_cons,List.not_mem_nil,or_false,or_self_left,or_self] using hm

theorem IsCSPolytope5.g2s2_last_small_seven
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 ≠ 8) : cnt P F 0 = 7 := by
  rcases hP.g2s2_last_row_cases hp hF h4 with hY | hD | hB
  · exact congrArg Row.n hY
  · exact congrArg Row.n hD
  · exact (hn (congrArg Row.n hB)).elim

theorem IsCSPolytope5.g2s2_last_full_b
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8) : faceRow P F = G2S4.bRow := by
  rcases hP.g2s2_last_row_cases hp hF h4 with hY | hD | hB
  · have he : cnt P F 0 = 7 := congrArg Row.n hY
    omega
  · have he : cnt P F 0 = 7 := congrArg Row.n hD
    omega
  · exact hB

theorem IsCSPolytope5.g2s2_last_no_big
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs)) (X : Set E5) : big2 P X = 0 := by
  let carrier : Row → Prop := fun R => R = G2S4.bRow
  apply hP.big2_zero_of_pair_support carrier hp (by decide +kernel) _ X
  intro F hF h4 hn
  rcases hP.g2s2_last_row_cases hp hF h4 with hY | hD | hB
  · have he := hP.exc_eq_faceRow hF h4
    rw [hY] at he
    norm_num [excRow] at he
    have ht := hP.Y_prism_count hF h4 hY
    exact hP.big2_zero_of_prism_exc_le_four (by omega) (by omega)
  · have he := hP.exc_eq_faceRow hF h4
    rw [hD] at he
    norm_num [G2S2.d36Row] at he
    -- D36 has polygon excess two; one large polygon would use at least two.
    have hq := hP.q4_add_big_le_exc F
    have hpy : tcnt P F (5,8,5) = 4 := by
      obtain ⟨hm,heq⟩ := hP.facet_rowX hF h4 (by have h7 : cnt P F 0 = 7 := congrArg Row.n hD; omega)
      have hk : ∀ Y ∈ smallRowsX, Y.1 = G2S2.d36Row → Y.2.1[1]?.getD 0 = 4 := by decide +kernel
      have ht := hk _ hm (by change rowOf F = _; rw [heq]; exact hD)
      rw [(hP.facet_profile hF h4 (by have h7 : cnt P F 0 = 7 := congrArg Row.n hD; omega)).2] at ht
      simp only [fv7,List.map_cons,List.map_nil,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] at ht
      rw [hP.tcnt_eq_card]
      exact ht
    obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (5,8,5))
    have hqt := (hP.q4_585 hT hT3 ht).1
    have hb : q4 P T ≤ q4 P F := Set.ncard_le_ncard
      (fun _ hQ => ⟨hQ.1,hQ.2.1.trans hTF,hQ.2.2⟩)
      (hP.faces_finite.subset fun Q hQ => hQ.1)
    omega
  · exact (hn hB).elim

end Kalai5
