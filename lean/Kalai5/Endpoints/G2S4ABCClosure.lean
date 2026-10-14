import Kalai5.Endpoints.FullPolygonLocalization
import Kalai5.Endpoints.G2S4BCClosure

namespace Kalai5
open Set
open scoped Classical

namespace G2S4
def abcWeight (R : Row) : ℕ :=
  if R = aRow then 6 else if R = bRow then 9 else q55QFourRowWeight R
end G2S4

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.g2s4_abc_row_cases
    (hp : (facetRows P).Perm (G2S4.abcPairs ++ G2S4.abcPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    faceRow P F = excRow ∨ faceRow P F = G2S4.aRow ∨
      faceRow P F = G2S4.bRow ∨ faceRow P F = G2S4.cRow := by
  have hm := hP.faceRow_mem_pair_rows hp hF h4
  simpa only [G2S4.abcPairs,List.mem_cons,List.not_mem_nil,or_false,or_self_left] using hm

theorem IsCSPolytope5.g2s4_abc_c_prism_zero
    (hp : (facetRows P).Perm (G2S4.abcPairs ++ G2S4.abcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hC : faceRow P F = G2S4.cRow) :
    tcnt P F (6,9,5) = 0 := by
  have hu := hP.facet_weight_le_context_upper hp (S := 4) (by simpa using hb) hF h4
  rw [hC] at hu
  have he : PrismBudget.contextUpper 4 G2S4.abcPairs G2S4.cRow = 7 := by decide +kernel
  rw [he] at hu
  by_contra hz
  have hn : cnt P F 0 = 8 := congrArg Row.n hC
  have hl := (hP.prism_weight_lower hF h4 hn (by omega)).2
  rw [hC] at hl
  norm_num [G2S4.cRow,PrismBudget.prismLower,PrismBudget.rowExcess] at hl
  omega

/-- Five Y pairs require a prism in the sole B pair by parity. -/
theorem IsCSPolytope5.g2s4_abc_b_prism_positive
    (hp : (facetRows P).Perm (G2S4.abcPairs ++ G2S4.abcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hB : faceRow P F = G2S4.bRow) :
    1 ≤ tcnt P F (6,9,5) := by
  by_contra hz
  have hzero : tcnt P F (6,9,5) = 0 := by omega
  have htwo : ((facetRows P).map fun R => if R = G2S4.bRow then 1 else 0).sum = 2 := by
    rw [(hp.map _).sum_eq]
    decide +kernel
  let value : Row → ℕ := fun R => if R = excRow then 1 else 0
  have hlocal : ∀ H ∈ faces P, dim H = 4 → (fun _ : Row => true) (faceRow P H) = true →
      tcnt P H (6,9,5) = value (faceRow P H) := by
    intro H hH hH4 _
    rcases hP.g2s4_abc_row_cases hp hH hH4 with hY | hA | hBr | hC
    · rw [hP.Y_prism_count hH hH4 hY,hY]
      rfl
    · rw [hP.small_rows_prism_free hH hH4 (by rw [hA]; decide +kernel),hA]
      rfl
    · have heq := hP.two_row_facets_eq_or_neg htwo hF h4 hB hH hH4 hBr
      have ht : tcnt P H (6,9,5) = 0 := by
        rcases heq with heq | heq
        · rwa [heq]
        · rw [heq,hP.tcnt_neg,hzero]
      rw [ht,hBr]
      rfl
    · rw [hP.g2s4_abc_c_prism_zero hp hb hH hH4 hC,hC]
      rfl
  have hpar := hP.facet_count_pair_row_parity (fun H => tcnt P H (6,9,5)) value
    (fun _ => true) hp hlocal (hP.four_dvd_sum_tcnt (6,9,5))
  have hbad : PrismBudget.rowParityOK value (fun _ => true) G2S4.abcPairs = false := by decide +kernel
  rw [hbad] at hpar
  contradiction

/-- The full B facet contains a prism and no large polygon. Localization
then rules out large polygons in every facet, including both A pairs. -/
theorem IsCSPolytope5.g2s4_abc_no_big
    (hv : fvec P 0 = 16)
    (hp : (facetRows P).Perm (G2S4.abcPairs ++ G2S4.abcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    (F : Set E5) : big2 P F = 0 := by
  have hm : G2S4.bRow ∈ facetRows P := hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel))
  obtain ⟨H,hH,hH4,hB⟩ := hP.mem_facetRows hm
  have hn : cnt P H 0 = 8 := congrArg Row.n hB
  have he := hP.exc_eq_faceRow hH hH4
  rw [hB] at he
  norm_num [G2S4.bRow] at he
  exact hP.big2_zero_of_full_facet hH hH4 (by omega)
    (hP.big2_zero_of_prism_exc_le_four (hP.g2s4_abc_b_prism_positive hp hb hH hH4 hB)
      (by omega)) F

theorem IsCSPolytope5.g2s4_abc_weight_lower
    (hv : fvec P 0 = 16)
    (hp : (facetRows P).Perm (G2S4.abcPairs ++ G2S4.abcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (G2S4.abcWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold G2S4.abcWeight
  split_ifs with hA hB
  · have hw := hP.a_weight_six_of_no_big hF h4 hA (hP.g2s4_abc_no_big hv hp hb F)
    omega
  · have hn : cnt P F 0 = 8 := congrArg Row.n hB
    have hl := (hP.prism_weight_lower hF h4 hn (hP.g2s4_abc_b_prism_positive hp hb hF h4 hB)).2
    rw [hB] at hl
    norm_num [G2S4.bRow,PrismBudget.prismLower,PrismBudget.rowExcess] at hl
    exact hl
  · exact hP.q55_qFour_row_weight hF h4

/-- Localization raises the pair weight to 69, exceeding the budget 66. -/
theorem IsCSPolytope5.g2s4_abc_false
    (hv : fvec P 0 = 16)
    (hp : (facetRows P).Perm (G2S4.abcPairs ++ G2S4.abcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132) : False := by
  have hm : G2S4.bRow ∈ facetRows P := hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel))
  obtain ⟨F,hF,h4,_⟩ := hP.mem_facetRows hm
  have hl := hP.g2s4_abc_weight_lower hv hp hb hF h4
  have hu := hP.twice_facet_weight_le_of_lower_bound G2S4.abcWeight
    (fun _ => hP.g2s4_abc_weight_lower hv hp hb) 132 hb hF h4
  have hs : ((facetRows P).map G2S4.abcWeight).sum = 138 := by
    rw [(hp.map G2S4.abcWeight).sum_eq]
    decide +kernel
  rw [hs] at hu
  omega

end Kalai5
