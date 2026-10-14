import Kalai5.Endpoints.PolygonPairSupport
import Kalai5.Endpoints.Ridge6117Budget

namespace Kalai5
open Set
open scoped Classical

namespace G2S4
def aRow : Row := ⟨7,16,16,7,32⟩
def dRow : Row := ⟨7,17,18,8,35⟩
def bRow : Row := ⟨8,19,19,8,38⟩
def cRow : Row := ⟨8,20,20,8,39⟩
def r35Pairs : List Row := [excRow,excRow,excRow,excRow,excRow,aRow,dRow,r35Row,cRow]
def r35Weight (R : Row) : ℕ := if R = aRow then 6 else PrismBudget.contextRowWeight r35Pairs R
end G2S4

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Extract the forced prism before using its quadrilaterals to remove
large polygons. This statement is independent of a weight budget. -/
theorem IsCSPolytope5.r35_forced_prism {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows)) (hf : PrismBudget.r35Forced rows)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = r35Row) :
    tcnt P F (6,9,5) = 1 := by
  have hother : ∀ H ∈ faces P, dim H = 4 → faceRow P H ≠ r35Row → tcnt P H (7,11,6) = 0 := by
    intro H hH hH4 hne
    have hm := hP.faceRow_mem_pair_rows hp hH hH4
    have hk := of_decide_eq_true ((List.all_eq_true.1 hf.2) _ hm)
    exact hP.no7116_row_count_zero hH hH4 (hk.resolve_left hne)
  have hz := hP.tcnt_zero_of_unique_pair_row hp hf.1 (7,11,6) hother hF h4
  have he := hP.r35_event_one hF h4 hR
  omega

theorem IsCSPolytope5.g2s4_r35_row_cases
    (hp : (facetRows P).Perm (G2S4.r35Pairs ++ G2S4.r35Pairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    faceRow P F = excRow ∨ faceRow P F = G2S4.aRow ∨ faceRow P F = G2S4.dRow ∨
      faceRow P F = r35Row ∨ faceRow P F = G2S4.cRow := by
  have hm := hP.faceRow_mem_pair_rows hp hF h4
  simpa only [G2S4.r35Pairs,List.mem_cons,List.not_mem_nil,or_false,or_self_left] using hm

/-- Only A and C could support a large polygon, but those are just two
antipodal pairs. A polygon requires at least three pairs. -/
theorem IsCSPolytope5.g2s4_r35_no_big
    (hp : (facetRows P).Perm (G2S4.r35Pairs ++ G2S4.r35Pairs)) (F : Set E5) : big2 P F = 0 := by
  let carrier : Row → Prop := fun R => R = G2S4.aRow ∨ R = G2S4.cRow
  apply hP.big2_zero_of_pair_support carrier hp (by decide +kernel) _ F
  intro H hH hH4 hf
  rcases hP.g2s4_r35_row_cases hp hH hH4 with hY | hA | hD | hR | hC
  · have he := hP.exc_eq_faceRow hH hH4
    rw [hY] at he
    norm_num [excRow] at he
    have ht := hP.Y_prism_count hH hH4 hY
    exact hP.big2_zero_of_prism_exc_le_four (by omega) (by omega)
  · exact (hf (Or.inl hA)).elim
  · have he := hP.exc_eq_faceRow hH hH4
    rw [hD] at he
    norm_num [G2S4.dRow] at he
    have hb := hP.q4_add_big_le_exc H
    omega
  · have he := hP.exc_eq_faceRow hH hH4
    rw [hR] at he
    norm_num [r35Row] at he
    have ht := hP.r35_forced_prism hp (by decide +kernel) hH hH4 hR
    exact hP.big2_zero_of_prism_exc_le_four (by omega) (by omega)
  · exact (hf (Or.inr hC)).elim

theorem IsCSPolytope5.g2s4_r35_weight_lower
    (hp : (facetRows P).Perm (G2S4.r35Pairs ++ G2S4.r35Pairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (G2S4.r35Weight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold G2S4.r35Weight
  split_ifs with hA
  · have hw := hP.a_weight_six_of_no_big hF h4 hA (hP.g2s4_r35_no_big hp F)
    omega
  · exact hP.context_row_weight_lower hp hF h4

theorem IsCSPolytope5.g2s4_r35_weight_eq
    (hp : (facetRows P).Perm (G2S4.r35Pairs ++ G2S4.r35Pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F = G2S4.r35Weight (faceRow P F) := by
  have hl := hP.g2s4_r35_weight_lower hp hF h4
  have hu := hP.twice_facet_weight_le_of_lower_bound G2S4.r35Weight
    (fun _ => hP.g2s4_r35_weight_lower hp) 132 hb hF h4
  have hs : ((facetRows P).map G2S4.r35Weight).sum = 132 := by
    rw [(hp.map G2S4.r35Weight).sum_eq]
    decide +kernel
  rw [hs] at hu
  omega

/-- After the polygon support constraint spends all remaining weight,
C needs a (6,11,7) ridge, but every other row pair forbids that type. -/
theorem IsCSPolytope5.g2s4_r35_false
    (hp : (facetRows P).Perm (G2S4.r35Pairs ++ G2S4.r35Pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132) : False := by
  have hother : ∀ H ∈ faces P, dim H = 4 → faceRow P H ≠ G2S4.cRow → tcnt P H (6,11,7) = 0 := by
    intro H hH hH4 hne
    rcases hP.g2s4_r35_row_cases hp hH hH4 with hY | hA | hD | hR | hC
    · exact hP.small_rows_6117_zero hH hH4 (by rw [hY]; decide +kernel)
    · exact hP.small_rows_6117_zero hH hH4 (by rw [hA]; decide +kernel)
    · have hw := hP.g2s4_r35_weight_eq hp hb hH hH4
      rw [hD] at hw
      have hf : G2S4.r35Weight G2S4.dRow = 0 := by decide +kernel
      rw [hf] at hw
      exact hP.tcnt_zero_of_small_weight (by decide) (by omega) (by norm_num; omega)
    · exact hP.r7_named_rows_6117_zero hH hH4 (Or.inl hR)
    · exact (hne hC).elim
  have hm : G2S4.cRow ∈ facetRows P := hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel))
  obtain ⟨F,hF,h4,hC⟩ := hP.mem_facetRows hm
  have hz := hP.tcnt_zero_of_unique_pair_row hp (by decide +kernel) (6,11,7) hother hF h4
  have hw := hP.g2s4_r35_weight_eq hp hb hF h4
  rw [hC] at hw
  have hf : G2S4.r35Weight G2S4.cRow = 3 := by decide +kernel
  rw [hf] at hw
  obtain ⟨_,_,_,_,_,_,_,_,h611,_,_⟩ := hP.c_weight_three_profile hF h4 hC (by omega)
  omega

end Kalai5
