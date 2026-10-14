import Kalai5.Endpoints.FullNinePolygon
import Kalai5.Endpoints.TwoPairPositiveFullPolygon

namespace Kalai5
open Set
open scoped Classical
namespace G2S2
def qRow : Row := ⟨8,20,21,9,42⟩
def nineQPairs : List Row := [excRow,excRow,excRow,excRow,excRow,excRow,G2S4.aRow,G2S4.bRow,qRow]
def nineQWeight (R : Row) : ℕ := if R = excRow then 9 else 6
end G2S2
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.g2s2_nine_q_row_cases
    (hp : (facetRows P).Perm (G2S2.nineQPairs ++ G2S2.nineQPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    faceRow P F = excRow ∨ faceRow P F = G2S4.aRow ∨ faceRow P F = G2S4.bRow ∨ faceRow P F = G2S2.qRow := by
  have hm := hP.faceRow_mem_pair_rows hp hF h4
  simpa only [G2S2.nineQPairs,List.mem_cons,List.not_mem_nil,or_false,or_self_left] using hm

theorem IsCSPolytope5.g2s2_nine_q_no_big
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S2.nineQPairs ++ G2S2.nineQPairs)) (X : Set E5) : big2 P X = 0 := by
  obtain ⟨F,hF,h4,hQ⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _
    (by decide +kernel : G2S2.qRow ∈ G2S2.nineQPairs)))
  obtain ⟨H,hH,hH4,hB⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _
    (by decide +kernel : G2S4.bRow ∈ G2S2.nineQPairs)))
  have hn : cnt P F 0 = 8 := congrArg Row.n hQ
  have hr : cnt P F 3 = 9 := congrArg Row.r hQ
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hB
  have hHr : cnt P H 3 = 8 := congrArg Row.r hB
  exact hP.full_nine_big2_zero hv hh hc hF h4 hn hr hH hH4 hH8
    (by intro he; rw [he,hr] at hHr; omega)
    (by intro he; rw [he,hP.cnt_neg,hr] at hHr; omega) X

theorem IsCSPolytope5.g2s2_nine_q_weight_lower
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S2.nineQPairs ++ G2S2.nineQPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (G2S2.nineQWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  have hz := hP.g2s2_nine_q_no_big hv hh hc hp F
  rcases hP.g2s2_nine_q_row_cases hp hF h4 with hY | hA | hB | hQ
  · have hb := hP.q55_qFour_row_weight hF h4
    rw [hY] at hb ⊢
    exact hb
  · have hw := hP.a_weight_six_of_no_big hF h4 hA hz
    rw [hA]
    change 6 ≤ _
    omega
  · have hb := hP.q55_qFour_row_weight hF h4
    rw [hB] at hb ⊢
    exact hb
  · have hb := hP.q_weight_four hF h4 hQ
    have he := hP.exc_eq_faceRow hF h4
    rw [hQ] at he
    norm_num [G2S2.qRow] at he
    have hq := hP.exc_eq_q4_of_big F hz
    have hw := hP.q55w_eq_b55 F
    rw [hQ]
    change 6 ≤ _
    omega

theorem IsCSPolytope5.g2s2_nine_q_weight_eq
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S2.nineQPairs ++ G2S2.nineQPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 144)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F = G2S2.nineQWeight (faceRow P F) := by
  have hl := hP.g2s2_nine_q_weight_lower hv hh hc hp hF h4
  have hu := hP.twice_facet_weight_le_of_lower_bound G2S2.nineQWeight
    (fun _ => hP.g2s2_nine_q_weight_lower hv hh hc hp) 144 hb hF h4
  have hs : ((facetRows P).map G2S2.nineQWeight).sum = 144 := by
    rw [(hp.map _).sum_eq]
    decide +kernel
  rw [hs] at hu
  omega

set_option maxHeartbeats 2000000 in
/-- Both full rows need a (6,10,6) ridge after their weights are fixed. -/
theorem IsCSPolytope5.g2s2_nine_q_full_6106_positive
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S2.nineQPairs ++ G2S2.nineQPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 144)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S4.bRow ∨ faceRow P F = G2S2.qRow) :
    1 ≤ tcnt P F (6,10,6) := by
  have hn : cnt P F 0 = 8 := by rcases hR with h | h <;> exact congrArg Row.n h
  have hw : q55w P F + 2 * exc P F = 6 := by
    have he := hP.g2s2_nine_q_weight_eq hv hh hc hp hb hF h4
    rcases hR with h | h <;> rw [h] at he <;> exact he
  have hpr : tcnt P F (6,9,5) = 0 := by
    by_contra hz
    have hl := (hP.prism_weight_lower hF h4 hn (by omega)).2
    rcases hR with h | h <;> rw [h] at hl
    all_goals norm_num [G2S4.bRow,G2S2.qRow,PrismBudget.prismLower,PrismBudget.rowExcess] at hl; omega
  rcases hR with hB | hQ
  · have hpos := hP.b_weight_six_special_ridge hF h4 hB hw.le
    have hz : tcnt P F (7,12,7) = 0 := by
      by_contra hz
      obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (7,12,7))
      simp only [tri3,Prod.mk.injEq] at ht
      have hl := hP.three_ridge_exc_le_weight hT hTF hT3 (by omega) (hP.g2s2_nine_q_no_big hv hh hc hp F)
      have he := hP.exc_threeface hT hT3
      rw [ht.2.1,ht.2.2] at he
      omega
    omega
  · have hr : cnt P F 3 = 9 := congrArg Row.r hQ
    have h7 : ∀ e p, tcnt P F (7,e,p) = 0 := by
      intro e p
      apply hP.full_nine_type_zero_of_small_free hv hh hc hF h4 hn hr (7,e,p) (by norm_num)
      intro H hH hH4 hHn
      have hsmall : cnt P H 0 ≤ 7 := by
        rcases hP.g2s2_nine_q_row_cases hp hH hH4 with hY | hA | hB | hQ
        · have := congrArg Row.n hY; change cnt P H 0 = 7 at this; omega
        · have := congrArg Row.n hA; change cnt P H 0 = 7 at this; omega
        · exact False.elim (hHn (congrArg Row.n hB))
        · exact False.elim (hHn (congrArg Row.n hQ))
      exact hP.small_facet_seven_ridge_zero hH hH4 hsmall e p
    have ha := h7 11 6
    have hd := h7 12 7
    have he := h7 13 8
    have hf := h7 14 9
    have hg := h7 15 10
    have hfp : cnt P F 2 = 21 := congrArg Row.p hQ
    have hj : incid P F 0 3 = 42 := congrArg Row.J hQ
    have hedge : cnt P F 1 = 20 := congrArg Row.e hQ
    obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
    by_contra hz
    have h610 : tcnt P F (6,10,6) = 0 := by omega
    have ht : tcnt P F (4,6,4) = 3 := by omega
    have htypes : ∀ T ∈ faces P, T ⊆ F → dim T = 3 → tri3 P T = (4,6,4) ∨ tri3 P T = (5,8,5) := by
      intro T hT hTF hT3
      have hlt := hP.cnt_zero_lt hT hF hTF (by intro heq; rw [heq,h4] at hT3; omega)
      have hm := hP.tri3_mem_fv8 hT hT3 (by omega)
      have hpos := hP.one_le_tcnt hT hTF hT3
      simp only [fv8,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      all_goals rw [h] at hpos; omega
    have hl := hP.three_tetrahedra_edges_twenty_two hF h4 hn ht htypes
    omega

end Kalai5
