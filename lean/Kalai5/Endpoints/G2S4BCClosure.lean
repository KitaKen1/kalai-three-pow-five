import Kalai5.Endpoints.G2S4BCStructure
import Kalai5.Endpoints.Full6106PyramidObstruction
import Kalai5.Endpoints.TwoPairPositivePolygonWeight

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Six Y pairs and the D/B/C pairs force four square pyramids in C,
but the shared (6,10,6) ridge permits only three. -/
theorem IsCSPolytope5.g2s4_bc_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S4.bcPairs ++ G2S4.bcPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 132) : False := by
  have hsmall : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 → cnt P X 0 = 7 := by
    intro X hX hX4 hn
    rcases hP.g2s4_bc_row_cases hp hX hX4 with hY | hD | hB | hC
    · exact congrArg Row.n hY
    · exact congrArg Row.n hD
    · exact False.elim (hn (congrArg Row.n hB))
    · exact False.elim (hn (congrArg Row.n hC))
  have hr : ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 → cnt P F 3 = 8 := by
    intro F hF hF4 hF8
    rcases hP.g2s4_bc_row_cases hp hF hF4 with hY | hD | hB | hC
    · have := congrArg Row.n hY; change cnt P F 0 = 7 at this; omega
    · have := congrArg Row.n hD; change cnt P F 0 = 7 at this; omega
    · exact congrArg Row.r hB
    · exact congrArg Row.r hC
  have hone : ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 →
      ∃ H, ∀ J ∈ faces P, dim J = 4 → cnt P J 0 = 8 → J ≠ F →
        (∃ T ∈ faces P, dim T = 3 ∧ T ⊆ F ∧ T ⊆ J) → J = H := by
    intro F hF hF4 hF8
    obtain ⟨H,T,hH,hH4,hHF,hHnF,hH8,_,_,ht,hTI⟩ := hP.g2s4_bc_full_partner hp hb hF hF4 hF8
    have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
    exact ⟨H,fun J hJ hJ4 hJ8 hJF hshare =>
      hP.full_six_partner_unique hv hc hF hF4 hF8 hH hH4 hH8 hHF hHnF hT6 hTI
        hJ hJ4 hJ8 hJF hshare⟩
  have hm : G2S4.cRow ∈ facetRows P := hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel))
  obtain ⟨F,hF,hF4,hFC⟩ := hP.mem_facetRows hm
  have hF8 : cnt P F 0 = 8 := congrArg Row.n hFC
  obtain ⟨H,T,hH,hH4,hHF,hHnF,hH8,hT,hT3,ht,hTI⟩ := hP.g2s4_bc_full_partner hp hb hF hF4 hF8
  have hpy := hP.g2s4_bc_c_pyramids_four hp hb hF hF4 hFC
  exact hP.full_6106_four_pyramids_false hv hh hc hsmall hr hone hF hF4 hF8 hH hH4 hH8
    hHF hHnF hT hT3 ht hTI (by omega)

theorem IsCSPolytope5.fewFull18_positive_g2s4_last_profile
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 4) :
    positivePairRows P = G2S4.abcPairs := by
  rcases hP.fewFull18_positive_g2s4_two_profiles hv hh h1 h6 hlt hS with hB | hA
  · have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
    rw [hB] at hp
    have hb := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
    rw [hS] at hb
    exact False.elim (hP.g2s4_bc_false hv hh
      (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).1 hp (by simpa using hb))
  · exact hA

namespace TwoPairPositiveProfile

def remainingProfilesNonadjacent : List (List Row) :=
  profilesPolygonWeightG2S2 ++ [G2S4.abcPairs]

omit hP in
theorem remainingProfilesNonadjacent_length : remainingProfilesNonadjacent.length = 10 := by
  rw [remainingProfilesNonadjacent,List.length_append,profilesPolygonWeightG2S2_length]
  rfl

end TwoPairPositiveProfile

theorem IsCSPolytope5.fewFull18_positive_nonadjacent_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesNonadjacent := by
  have hc := hP.fewFull18_positive_two_cells hv hh h1 h6 hlt
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hc
  rcases hc with h | h
  · apply List.mem_append_left
    have hm := hP.fewFull18_positive_polygon_cell_profile_mem hv hh h1 h6 hlt
    have hn := hP.fewFull18_positive_g2s2_r0_ne hv hh h1 h6 hlt h.2
    rw [h.1,h.2] at hm
    simpa only [TwoPairPositiveProfile.profilesPolygonWeightG2S2,List.mem_filter,
      bne_iff_ne, Bool.true_eq] using And.intro hm hn
  · apply List.mem_append_right
    rw [hP.fewFull18_positive_g2s4_last_profile hv hh h1 h6 hlt h.2]
    exact List.mem_singleton_self _

end Kalai5

