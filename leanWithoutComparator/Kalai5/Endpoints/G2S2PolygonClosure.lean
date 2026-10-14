import Kalai5.Endpoints.FullPolygonRowBudget

namespace Kalai5
open Set
open scoped Classical

namespace G2S2
def polygonPairs11 : List Row := [excRow,excRow,excRow,excRow,G2S4.aRow,G2S4.aRow,G2S4.aRow,⟨8,18,17,7,35⟩,⟨8,19,19,8,39⟩]
def polygonPairs15 : List Row := [excRow,excRow,excRow,excRow,excRow,G2S4.aRow,G2S4.aRow,⟨8,18,17,7,35⟩,⟨8,20,21,9,42⟩]
def polygonPairs19 : List Row := [excRow,excRow,excRow,excRow,G2S4.aRow,G2S4.aRow,G2S4.aRow,⟨8,18,17,7,36⟩,⟨8,19,19,8,38⟩]
def polygonPairs31 : List Row := [excRow,excRow,excRow,excRow,excRow,G2S4.aRow,G2S4.aRow,⟨8,19,19,8,38⟩,⟨8,19,19,8,39⟩]
def polygonExcluded : List (List Row) := [polygonPairs11,polygonPairs15,polygonPairs19,polygonPairs31]
end G2S2

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Each of the four profiles has a full facet forbidding large polygons.
The resulting A weights exceed the pair budget of 72. -/
theorem IsCSPolytope5.g2s2_polygon_profile_false (hv : fvec P 0 = 16)
    {rows : List Row} (hp : (facetRows P).Perm (rows ++ rows))
    (hm : rows ∈ G2S2.polygonExcluded)
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 144) : False := by
  simp only [G2S2.polygonExcluded,List.mem_cons,List.not_mem_nil,or_false] at hm
  have hz : ∀ F, big2 P F = 0 := by
    rcases hm with rfl | rfl | rfl | rfl
    · exact hP.big2_zero_of_full_v_row hv (hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel)))
    · exact hP.big2_zero_of_full_r35_forced hv hp (by decide +kernel) (by decide +kernel)
    · exact hP.big2_zero_of_full_r0_row hv (hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel)))
    · exact hP.big2_zero_of_full_v_row hv (hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel)))
  have hbudget := hP.polygon_free_pair_weight_budget hp hz (S := 2) (by simpa using hb)
  have hlarge : 72 < (rows.map (PrismBudget.polygonFreeWeight rows)).sum := by
    rcases hm with rfl | rfl | rfl | rfl <;> decide +kernel
  omega

end Kalai5
