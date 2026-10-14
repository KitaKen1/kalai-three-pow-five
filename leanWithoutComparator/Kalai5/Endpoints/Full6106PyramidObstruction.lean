import Kalai5.Endpoints.FullSixPyramidBound

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A shared (6,10,6) ridge leaves one nonadjacent slot and at most two
quadrilaterals, so its full facet can have at most three square pyramids. -/
theorem IsCSPolytope5.full_6106_pyramids_le_three
    (hv : fvec P 0 = 16) (hc : cnt8 (facetRows P) = 4)
    (hsmall : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 → cnt P X 0 = 7)
    (hdeg : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 →
      {J | J ∈ faces P ∧ dim J = 4 ∧ cnt P J 0 = 8 ∧
        ∃ U ∈ faces P, dim U = 3 ∧ U ⊆ J ∧ U ⊆ X}.ncard = 2)
    {F H T : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHr : cnt P H 3 = 8) (hHF : H ≠ F) (hHnF : H ≠ -F)
    (hT : T ∈ faces P) (hT3 : dim T = 3)
    (ht : tri3 P T = (6,10,6)) (hTI : T = F ∩ H) :
    tcnt P F (5,8,5) ≤ 3 := by
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have hTe : cnt P T 1 = 10 := congrArg (fun t => t.2.1) ht
  have hTp : cnt P T 2 = 6 := congrArg (fun t => t.2.2) ht
  have hb := hP.full_six_pyramid_count_le hv hc hsmall hdeg hF hF4 hF8 hH hH4 hH8
    hHF hHnF hT hT3 hT6 hTI (by omega)
  have he := hP.exc_threeface hT hT3
  rw [hTe,hTp] at he
  have hq := hP.q4_add_big_le_exc T
  omega

/-- An eight-ridge configuration with saturated full degree cannot
contain four square pyramids opposite a shared (6,10,6) ridge. -/
theorem IsCSPolytope5.full_6106_four_pyramids_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hsmall : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 → cnt P X 0 = 7)
    (hr : ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 → cnt P F 3 = 8)
    (hone : ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 →
      ∃ H, ∀ J ∈ faces P, dim J = 4 → cnt P J 0 = 8 → J ≠ F →
        (∃ T ∈ faces P, dim T = 3 ∧ T ⊆ F ∧ T ⊆ J) → J = H)
    {F H T : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F)
    (hT : T ∈ faces P) (hT3 : dim T = 3)
    (ht : tri3 P T = (6,10,6)) (hTI : T = F ∩ H)
    (hpy : 4 ≤ tcnt P F (5,8,5)) : False := by
  have hb := hP.full_6106_pyramids_le_three hv hc hsmall
    (fun _ => hP.full_ridge_saturation_four hv hh hc hr hone)
    hF hF4 hF8 hH hH4 hH8 (hr H hH hH4 hH8) hHF hHnF hT hT3 ht hTI
  omega

end Kalai5

