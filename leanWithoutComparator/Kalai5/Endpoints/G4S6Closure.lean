import Kalai5.Endpoints.G4S6Partners
import Kalai5.Endpoints.FullPairExhaust
import Kalai5.Endpoints.FullRidgeSaturation

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The unique positive (G,Gs)=(4,6) profile is geometrically impossible.
Full-facet degree saturation contradicts the neighbour of a square pyramid
which contains both vertices outside the six-vertex shared ridge. -/
theorem IsCSPolytope5.fewFull18_positive_g4s6_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 6) : False := by
  have hc := (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).1
  have hr : ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 → cnt P F 3 = 8 := by
    intro F hF hF4 hF8
    exact congrArg Row.r (hP.fewFull18_positive_g4s6_full_profile hv hh h1 h6 hlt hG hS hF hF4 hF8).1
  have hone : ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 →
      ∃ H, ∀ J ∈ faces P, dim J = 4 → cnt P J 0 = 8 → J ≠ F →
        (∃ T ∈ faces P, dim T = 3 ∧ T ⊆ F ∧ T ⊆ J) → J = H := by
    intro F hF hF4 hF8
    obtain ⟨H,T,hH,hH4,hHF,hHnF,hHC,_,_,ht,hTI,_,_⟩ :=
      hP.fewFull18_positive_g4s6_C_partner hv hh h1 h6 hlt hG hS hF hF4 hF8
    have hH8 : cnt P H 0 = 8 := congrArg Row.n hHC
    have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
    exact ⟨H,fun J hJ hJ4 hJ8 hJF hshare =>
      hP.full_six_partner_unique hv hc hF hF4 hF8 hH hH4 hH8 hHF hHnF hT6 hTI
        hJ hJ4 hJ8 hJF hshare⟩
  have hfull : {F | F ∈ faces P ∧ dim F = 4 ∧ cnt P F 0 = 8}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [← hP.cnt8_eq_full_ncard,hc]; decide)
  obtain ⟨F,hF,hF4,hF8⟩ := hfull
  obtain ⟨H,T,hH,hH4,hHF,hHnF,hHC,hT,hT3,ht,hTI,_,_⟩ :=
    hP.fewFull18_positive_g4s6_C_partner hv hh h1 h6 hlt hG hS hF hF4 hF8
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHC
  have hHr : cnt P H 3 = 8 := congrArg Row.r hHC
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have hTp : cnt P T 2 = 7 := congrArg (fun t => t.2.2) ht
  have hTF : T ⊆ F := hTI ▸ inter_subset_left
  obtain ⟨hFC,_,_,_,_,hpyr,_⟩ :=
    hP.fewFull18_positive_g4s6_full_profile hv hh h1 h6 hlt hG hS hF hF4 hF8
  obtain ⟨R,hR,hRF,hR3,hrR,_,_,hi3⟩ :=
    hP.C_exists_pyramid_triangle hF hF4 hFC hT hTF hT3 ht (by omega)
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
    rcases hP.fewFull18_positive_g4s6_rows hv hh h1 h6 hlt hG hS hX hX4 with he | he | he
    · exact congrArg Row.n he
    · exact congrArg Row.n he
    · exact False.elim (hX8 (congrArg Row.n he))
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
  have hb := Set.ncard_le_ncard hs (Set.finite_singleton F)
  rw [hdeg,Set.ncard_singleton] at hb
  omega

theorem IsCSPolytope5.fewFull18_positive_five_cells
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    ((flagDataOf P).G,(flagDataOf P).Gs) ∈ [(2,2),(2,4),(2,6),(2,8),(4,2)] := by
  have hc := hP.fewFull18_positive_six_cells hv hh h1 h6 hlt
  have hn : ((flagDataOf P).G,(flagDataOf P).Gs) ≠ ((4,6) : ℤ × ℤ) := by
    intro he
    exact hP.fewFull18_positive_g4s6_false hv hh h1 h6 hlt
      (congrArg Prod.fst he) (congrArg Prod.snd he)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  tauto

end Kalai5
