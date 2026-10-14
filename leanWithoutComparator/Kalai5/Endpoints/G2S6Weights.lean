import Kalai5.Endpoints.CContextSupport
import Kalai5.Endpoints.RidgePolygonCapacity

namespace Kalai5
open Set
open scoped Classical

namespace G2S6

def dRow : Row := ⟨7,17,18,8,35⟩
def hRow : Row := ⟨8,20,20,8,38⟩
def cRow : Row := ⟨8,20,20,8,39⟩

def pairs : List Row := [excRow,excRow,excRow,excRow,excRow,excRow,dRow,hRow,cRow]

def rowWeight (R : Row) : ℕ := if R = hRow then 3 else q55QFourRowWeight R

end G2S6

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.g2s6_row_cases
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    faceRow P F = excRow ∨ faceRow P F = G2S6.dRow ∨
      faceRow P F = G2S6.hRow ∨ faceRow P F = G2S6.cRow := by
  have hm := hP.faceRow_mem_pair_rows hp hF h4
  simpa only [G2S6.pairs,List.mem_cons,List.not_mem_nil,or_false,or_self_left] using hm

theorem IsCSPolytope5.g2s6_c_bipyr_zero
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.cRow) : tcnt P F (5,9,6) = 0 := by
  exact hP.c_support_bipyr_zero hp (S := 6) (by simpa using hb)
    (by decide +kernel) hF h4 hR

/-- C carries no bipyramids. Thus H and D are the only two possible
antipodal carrier pairs, and H has at most one bipyramid. -/
theorem IsCSPolytope5.g2s6_h_bipyr_le_one
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.hRow) : tcnt P F (5,9,6) ≤ 1 := by
  let carrier : Row → Prop := fun R => R = G2S6.dRow ∨ R = G2S6.hRow
  have hfree : ∀ H ∈ faces P, dim H = 4 → ¬ carrier (faceRow P H) →
      ∀ t ∈ [(5,9,6)], tcnt P H t = 0 := by
    intro H hH hH4 hf t ht
    simp only [List.mem_singleton] at ht
    subst t
    rcases hP.g2s6_row_cases hp hH hH4 with hY | hD | hHrow | hC
    · exact hP.bipyr_free_rows_count_zero hH hH4 (by rw [hY]; decide +kernel)
    · exact (hf (Or.inl hD)).elim
    · exact (hf (Or.inr hHrow)).elim
    · exact hP.g2s6_c_bipyr_zero hp hb hH hH4 hC
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hc := hP.ridge_type_pair_capacity carrier [(5,9,6)] (by decide) hp hfree
    hF h4 (Or.inr hR) (by
      intro t ht u hu
      simp only [List.mem_singleton] at ht hu
      subst t
      subst u
      omega)
  have hk : (G2S6.pairs.filter fun R => decide (carrier R)).length = 2 := by decide +kernel
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hk] at hc
  omega

/-- Low weight removes all exceptional types except (6,11,7). The flag
gap of H then requires two bipyramids if its weight were below three. -/
theorem IsCSPolytope5.g2s6_h_weight_three_lower
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.hRow) : 3 ≤ q55w P F + 2 * exc P F := by
  have hbi := hP.g2s6_h_bipyr_le_one hp hb hF h4 hR
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hr : cnt P F 3 = 8 := congrArg Row.r hR
  have hfp : cnt P F 2 = 20 := congrArg Row.p hR
  have hj : incid P F 0 3 = 38 := congrArg Row.J hR
  have he : exc P F = 2 := by
    have he := hP.exc_eq_faceRow hF h4
    rw [hR] at he
    norm_num [G2S6.hRow] at he
    exact he
  by_contra hh
  have h610 : tcnt P F (6,10,6) = 0 :=
    hP.tcnt_zero_of_small_weight (by decide) (by omega) (by norm_num; omega)
  have h611 : tcnt P F (6,11,7) = 0 :=
    hP.tcnt_zero_of_small_weight (by decide) (by omega) (by norm_num; omega)
  have h612 : tcnt P F (6,12,8) = 0 :=
    hP.tcnt_zero_of_polygon_count hF h4 (by change cnt P F 3 ≤ 8; omega)
  have h7 := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn (by omega)
  have h7a := h7 11 6
  have h7b := h7 12 7
  have h7c := h7 13 8
  have h7d := h7 14 9
  have h7e := h7 15 10
  have hpr := hP.h20_no_prism hF h4 hR
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  omega

theorem IsCSPolytope5.g2s6_row_weight_lower
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (G2S6.rowWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold G2S6.rowWeight
  split_ifs with hR
  · exact hP.g2s6_h_weight_three_lower hp hb hF h4 hR
  · exact hP.q55_qFour_row_weight hF h4

/-- Six Y pairs spend 54, and H and C spend three each. The pair budget
is exactly 60, so all these lower bounds are equalities, including D=0. -/
theorem IsCSPolytope5.g2s6_weight_eq
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F = G2S6.rowWeight (faceRow P F) := by
  have hl := hP.g2s6_row_weight_lower hp hb hF h4
  have hu := hP.twice_facet_weight_le_of_lower_bound G2S6.rowWeight
    (fun _ => hP.g2s6_row_weight_lower hp hb) 120 hb hF h4
  have hs : ((facetRows P).map G2S6.rowWeight).sum = 120 := by
    rw [(hp.map G2S6.rowWeight).sum_eq]
    decide +kernel
  rw [hs] at hu
  omega

end Kalai5
