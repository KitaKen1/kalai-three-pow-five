import Kalai5.Endpoints.FullPolygonLocalization
import Kalai5.Endpoints.G2S4R35

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget
def polygonFreeWeight (rows : List Row) (R : Row) : ℕ :=
  if R = G2S4.aRow then 6 else contextRowWeight rows R
end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.big2_zero_of_full_v_row (hv : fvec P 0 = 16)
    (hm : (⟨8,19,19,8,39⟩ : Row) ∈ facetRows P) (F : Set E5) : big2 P F = 0 := by
  obtain ⟨H,hH,h4,hR⟩ := hP.mem_facetRows hm
  have hn : cnt P H 0 = 8 := congrArg Row.n hR
  have ht := hP.v_prism_count_one hH h4 hR
  have he := hP.exc_eq_faceRow hH h4
  rw [hR] at he
  norm_num at he
  exact hP.big2_zero_of_full_facet hH h4 (by omega)
    (hP.big2_zero_of_prism_exc_le_four (by omega) (by omega)) F

theorem IsCSPolytope5.big2_zero_of_full_r0_row (hv : fvec P 0 = 16)
    (hm : r0Row ∈ facetRows P) (F : Set E5) : big2 P F = 0 := by
  obtain ⟨H,hH,h4,hR⟩ := hP.mem_facetRows hm
  have hn : cnt P H 0 = 8 := congrArg Row.n hR
  have ht := (hP.r0_types hH h4 hR).2.2.1
  have he := hP.exc_eq_faceRow hH h4
  rw [hR] at he
  norm_num [r0Row] at he
  have hq := hP.b55_add_five_le_of_two_prisms (by omega : 2 ≤ tcnt P H (6,9,5))
  have hb := hP.q4_add_big_le_exc H
  exact hP.big2_zero_of_full_facet hH h4 (by omega) (by omega) F

theorem IsCSPolytope5.big2_zero_of_full_r35_forced (hv : fvec P 0 = 16)
    {rows : List Row} (hp : (facetRows P).Perm (rows ++ rows))
    (hf : PrismBudget.r35Forced rows) (hm : r35Row ∈ rows) (F : Set E5) : big2 P F = 0 := by
  obtain ⟨H,hH,h4,hR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _ hm))
  have hn : cnt P H 0 = 8 := congrArg Row.n hR
  have ht := hP.r35_forced_prism hp hf hH h4 hR
  have he := hP.exc_eq_faceRow hH h4
  rw [hR] at he
  norm_num [r35Row] at he
  exact hP.big2_zero_of_full_facet hH h4 (by omega)
    (hP.big2_zero_of_prism_exc_le_four (by omega) (by omega)) F

theorem IsCSPolytope5.polygon_free_row_weight {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows)) (hz : ∀ F, big2 P F = 0)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (PrismBudget.polygonFreeWeight rows (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold PrismBudget.polygonFreeWeight
  split_ifs with hA
  · have hw := hP.a_weight_six_of_no_big hF h4 hA (hz F)
    omega
  · exact hP.context_row_weight_lower hp hF h4

theorem IsCSPolytope5.polygon_free_pair_weight_budget {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows)) (hz : ∀ F, big2 P F = 0)
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S) :
    ((rows.map (PrismBudget.polygonFreeWeight rows)).sum : ℤ) ≤ 78 - 3 * S := by
  have hs : (((facetRows P).map (PrismBudget.polygonFreeWeight rows)).sum : ℤ) ≤ 156 - 6 * S := by
    rw [hP.facetRows_sum,Nat.cast_sum]
    apply (Finset.sum_le_sum (fun F hF => ?_)).trans hb
    rw [Set.Finite.mem_toFinset] at hF
    exact hP.polygon_free_row_weight hp hz hF.1 hF.2
  rw [(hp.map _).sum_eq,List.map_append,List.sum_append,Nat.cast_add] at hs
  omega

end Kalai5
