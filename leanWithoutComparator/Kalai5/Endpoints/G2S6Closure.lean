import Kalai5.Endpoints.G2S6Partners
import Kalai5.Endpoints.FullPairExhaust
import Kalai5.Endpoints.FullRidgeSaturation

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The rigid Gs=6 profile has the same degree-saturation obstruction as
the former G=4 cell: a C pyramid forces a small facet to miss a full pair. -/
theorem IsCSPolytope5.fewFull18_positive_g2s6_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 6) : False := by
  have hp := hP.fewFull18_positive_g2s6_profile hv hh h1 h6 hlt hS
  have hbudget := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  rw [hS] at hbudget
  have hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120 :=
    by simpa using hbudget
  have hc := (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).1
  have hr : ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 → cnt P F 3 = 8 := by
    intro F hF hF4 hF8
    rcases hP.g2s6_row_cases hp hF hF4 with hY | hD | hH | hC
    · have := congrArg Row.n hY
      change cnt P F 0 = 7 at this
      omega
    · have := congrArg Row.n hD
      change cnt P F 0 = 7 at this
      omega
    · exact congrArg Row.r hH
    · exact congrArg Row.r hC
  have hone : ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 →
      ∃ H, ∀ J ∈ faces P, dim J = 4 → cnt P J 0 = 8 → J ≠ F →
        (∃ T ∈ faces P, dim T = 3 ∧ T ⊆ F ∧ T ⊆ J) → J = H := by
    intro F hF hF4 hF8
    obtain ⟨H,T,hH,hH4,hHF,hHnF,hH8,_,_,ht,hTI⟩ := hP.g2s6_full_partner hp hb hF hF4 hF8
    have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
    exact ⟨H,fun J hJ hJ4 hJ8 hJF hshare =>
      hP.full_six_partner_unique hv hc hF hF4 hF8 hH hH4 hH8 hHF hHnF hT6 hTI
        hJ hJ4 hJ8 hJF hshare⟩
  have hm : G2S6.cRow ∈ facetRows P := hp.mem_iff.2
    (List.mem_append_left _ (by decide +kernel))
  obtain ⟨F,hF,hF4,hFC⟩ := hP.mem_facetRows hm
  have hF8 : cnt P F 0 = 8 := congrArg Row.n hFC
  obtain ⟨H,T,hH,hH4,hHF,hHnF,hH8,hT,hT3,ht,hTI⟩ := hP.g2s6_full_partner hp hb hF hF4 hF8
  have hHr : cnt P H 3 = 8 := hr H hH hH4 hH8
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have hTp : cnt P T 2 = 7 := congrArg (fun t => t.2.2) ht
  have hTF : T ⊆ F := hTI ▸ inter_subset_left
  have hprof := (hP.g2s6_c_ridge_profile hp hb hF hF4 hFC).2.2.2
  have hpyr : 2 ≤ tcnt P F (5,8,5) := by
    simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq] at hprof
    omega
  obtain ⟨R,hR,hRF,hR3,hrR,_,_,hi3⟩ :=
    hP.C_exists_pyramid_triangle hF hF4 hFC hT hTF hT3 ht hpyr
  have hR5 : cnt P R 0 = 5 := congrArg Prod.fst hrR
  obtain ⟨X,hX,hX4,hXF,hRX⟩ := hP.exists_other_facet hR hR3 hRF
  have hX8 : cnt P X 0 ≠ 8 := by
    intro h8
    have hXH := hP.full_six_partner_unique hv hc hF hF4 hF8 hH hH4 hH8 hHF hHnF hT6 hTI
      hX hX4 h8 hXF ⟨R,hR,hR3,hRF,hRX⟩
    have he : R = T := (hP.three_face_eq_inter hF hF4 hH hH4 hHF.symm hR hR3
      hRF (hXH ▸ hRX)).trans hTI.symm
    rw [he] at hR5
    omega
  have hX7 : cnt P X 0 = 7 := by
    rcases hP.g2s6_row_cases hp hX hX4 with hY | hD | hH | hC
    · exact congrArg Row.n hY
    · exact congrArg Row.n hD
    · exact False.elim (hX8 (congrArg Row.n hH))
    · exact False.elim (hX8 (congrArg Row.n hC))
  have hobs := hP.full_pyramid_partner_obstruction hv hF hF4 hF8 hH hH4 hH8 hHr
    hT hT3 hT6 hTp hTI hRF hR5 hi3 hX hX4 hX7 hRX
  have hdeg := hP.full_ridge_saturation_four hv hh hc hr hone hX hX4 hX8
  have hs : {J | J ∈ faces P ∧ dim J = 4 ∧ cnt P J 0 = 8 ∧
      ∃ U ∈ faces P, dim U = 3 ∧ U ⊆ J ∧ U ⊆ X} ⊆ {F} := by
    rintro J ⟨hJ,hJ4,hJ8,U,hU,hU3,hUJ,hUX⟩
    rcases hP.four_full_exhaust hc hF hF4 hF8 hH hH4 hH8 hHF hHnF hJ hJ4 hJ8 with
      he | he | he | he
    · exact he
    · have hd := hP.disjoint_neg_of_full hF (hP.ne_of_dim_ne' (by rw [hF4]; decide)) (by omega)
      have hRU : Disjoint R U := Set.disjoint_of_subset hRF (he ▸ hUJ) hd
      have := hP.eight_le_cnt_of_disjoint hX hR hR3 hU hU3 hRX hUX hRU
      omega
    · exact False.elim ((hobs U hU hU3 hUX).1 (he ▸ hUJ))
    · exact False.elim ((hobs U hU hU3 hUX).2 (he ▸ hUJ))
  have hbound := Set.ncard_le_ncard hs (Set.finite_singleton F)
  rw [hdeg,Set.ncard_singleton] at hbound
  omega

theorem IsCSPolytope5.fewFull18_positive_two_cells
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    ((flagDataOf P).G,(flagDataOf P).Gs) ∈ ([(2,2),(2,4)] : List (ℤ × ℤ)) := by
  have hc := hP.fewFull18_positive_polygon_three_cells hv hh h1 h6 hlt
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hc ⊢
  rcases hc with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (hP.fewFull18_positive_g2s6_false hv hh h1 h6 hlt h.2)

namespace TwoPairPositiveProfile

def remainingProfilesTwoCells : List (List Row) := profilesPolygon 2 2 ++ profilesPolygon 2 4

omit hP in
theorem remainingProfilesTwoCells_length : remainingProfilesTwoCells.length = 13 := by
  have hc := profilePolygon_counts
  simp only [cellsG2,List.map_cons,List.map_nil,List.cons.injEq] at hc
  rw [remainingProfilesTwoCells,List.length_append,hc.1,hc.2.1]

end TwoPairPositiveProfile

theorem IsCSPolytope5.fewFull18_positive_two_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesTwoCells := by
  have hm := hP.fewFull18_positive_polygon_cell_profile_mem hv hh h1 h6 hlt
  have hc := hP.fewFull18_positive_two_cells hv hh h1 h6 hlt
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hc
  rcases hc with h | h
  · exact List.mem_append_left _ (by simpa only [h.1,h.2] using hm)
  · exact List.mem_append_right _ (by simpa only [h.1,h.2] using hm)

end Kalai5
