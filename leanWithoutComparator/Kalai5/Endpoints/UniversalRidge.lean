import Kalai5.Endpoints.TwoPairPositiveG4S6

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- If T has as many polygon faces as F has other ridges, it is adjacent
to every other ridge of F. -/
theorem IsCSPolytope5.universal_ridge_of_count
    {F T R : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (hc : cnt P T 2 + 1 = cnt P F 3)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3) (hRT : R ≠ T) :
    T ∩ R ∈ faces P ∧ dim (T ∩ R) = 2 := by
  have hother : ∀ Q ∈ {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2},
      ∃ S ∈ {S | S ∈ faces P ∧ Q ⊆ S ∧ S ⊆ F ∧ dim S = 3}, S ≠ T := by
    intro Q hQ
    exact exists_ne_of_ncard_eq_two (hP.twoface_in_facet hF hF4 hQ.1
      (hQ.2.1.trans hTF) hQ.2.2) ⟨hT,hQ.2.1,hTF,hT3⟩
  choose! f hf hfT using hother
  have hi : Set.InjOn f {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2} := by
    intro Q hQ U hU he
    obtain ⟨hS,hQS,_,hS3⟩ := hf Q hQ
    obtain ⟨hV,hUV,_,hV3⟩ := hf U hU
    have hq := hP.inter_three_eq hQ.1 hQ.2.2 hT hT3 hS hS3 (hfT Q hQ).symm hQ.2.1 hQS
    have hu := hP.inter_three_eq hU.1 hU.2.2 hT hT3 hV hV3 (hfT U hU).symm hU.2.1 hUV
    exact hq.symm.trans ((congrArg (fun S => T ∩ S) he).trans hu)
  have hm : f '' {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2} ⊆
      {S | S ∈ faces P ∧ S ⊆ F ∧ dim S = 3} \ {T} := by
    rintro S ⟨Q,hQ,rfl⟩
    obtain ⟨hS,_,hSF,hS3⟩ := hf Q hQ
    exact ⟨⟨hS,hSF,hS3⟩,hfT Q hQ⟩
  have hn : (f '' {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2}).ncard = cnt P T 2 :=
    hi.ncard_image
  have hb : ({S | S ∈ faces P ∧ S ⊆ F ∧ dim S = 3} \ {T}).ncard = cnt P F 3 - 1 :=
    Set.ncard_sdiff_singleton_of_mem ⟨hT,hTF,hT3⟩
  have he := Set.eq_of_subset_of_ncard_le hm (by rw [hn,hb]; omega) (hP.below_finite F 3).sdiff
  have hr : R ∈ f '' {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2} := by
    rw [he]
    exact ⟨⟨hR,hRF,hR3⟩,hRT⟩
  obtain ⟨Q,hQ,hQR⟩ := hr
  have hQS := (hf Q hQ).2.1
  have heq := hP.inter_three_eq hQ.1 hQ.2.2 hT hT3 hR hR3 hRT.symm hQ.2.1 (hQR ▸ hQS)
  rw [heq]
  exact ⟨hQ.1,hQ.2.2⟩

theorem IsCSPolytope5.universal_ridge_tetra_inter
    {F T R : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (hc : cnt P T 2 + 1 = cnt P F 3)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3)
    (hR4 : cnt P R 0 = 4) (hRT : R ≠ T) : cnt P (T ∩ R) 0 = 3 := by
  obtain ⟨hQ,hQ2⟩ := hP.universal_ridge_of_count hF hF4 hT hTF hT3 hc hR hRF hR3 hRT
  have hlo := hP.three_le_cnt hQ hQ2
  have hne : T ∩ R ≠ R := by intro he; rw [he,hR3] at hQ2; omega
  have hhi := hP.cnt_zero_lt hQ hR inter_subset_right hne
  omega

theorem IsCSPolytope5.ridge_partner_unique_inside
    {F T R S Q : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hQ : Q ∈ faces P) (hQF : Q ⊆ F) (hQ2 : dim Q = 2)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (hQT : Q ⊆ T)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3) (hQR : Q ⊆ R) (hRT : R ≠ T)
    (hS : S ∈ faces P) (hSF : S ⊆ F) (hS3 : dim S = 3) (hQS : Q ⊆ S) (hST : S ≠ T) : R = S := by
  by_contra hRS
  have hs : ({T,R,S} : Set (Set E5)) ⊆
      {U | U ∈ faces P ∧ Q ⊆ U ∧ U ⊆ F ∧ dim U = 3} := by
    intro U hU
    rcases hU with rfl | rfl | rfl
    · exact ⟨hT,hQT,hTF,hT3⟩
    · exact ⟨hR,hQR,hRF,hR3⟩
    · exact ⟨hS,hQS,hSF,hS3⟩
  have hl := Set.ncard_le_ncard hs (hP.faces_finite.subset fun U hU => hU.1)
  rw [Set.ncard_eq_three.2 ⟨T,R,S,hRT.symm,hST.symm,hRS,rfl⟩,
    hP.twoface_in_facet hF hF4 hQ hQF hQ2] at hl
  omega

theorem IsCSPolytope5.q4_6117 {T : Set E5}
    (hT : T ∈ faces P) (hT3 : dim T = 3) (ht : tri3 P T = (6,11,7)) :
    q4 P T = 1 ∧ big2 P T = 0 := by
  simp only [tri3,Prod.mk.injEq] at ht
  have he := hP.exc_threeface hT hT3
  rw [ht.2.1,ht.2.2] at he
  have hb := hP.q4_add_big_le_exc T
  have hb0 : big2 P T = 0 := by omega
  have hq := hP.exc_eq_q4_of_big T hb0
  exact ⟨by omega,hb0⟩

/-- One of the square pyramids meets T in a triangle and uses both vertices
of F outside T. -/
theorem IsCSPolytope5.C_exists_pyramid_triangle
    {F T : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hFR : faceRow P F = ⟨8,20,20,8,39⟩)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (ht : tri3 P T = (6,11,7))
    (hpyr : 2 ≤ tcnt P F (5,8,5)) :
    ∃ R, R ∈ faces P ∧ R ⊆ F ∧ dim R = 3 ∧ tri3 P R = (5,8,5) ∧
      T ∩ R ∈ faces P ∧ dim (T ∩ R) = 2 ∧ cnt P (T ∩ R) 0 = 3 := by
  have hc : cnt P T 2 + 1 = cnt P F 3 := by
    have h7 : cnt P T 2 = 7 := congrArg (fun t => t.2.2) ht
    have h8 : cnt P F 3 = 8 := congrArg Row.r hFR
    omega
  obtain ⟨R,S,hRS,⟨hR,hRF,hR3,hr⟩,⟨hS,hSF,hS3,hs⟩⟩ := hP.exists_two_of_tcnt hpyr
  have hR5 : cnt P R 0 = 5 := congrArg Prod.fst hr
  have hS5 : cnt P S 0 = 5 := congrArg Prod.fst hs
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have hRT : R ≠ T := by rintro rfl; omega
  have hST : S ≠ T := by rintro rfl; omega
  obtain ⟨hQ,hQ2⟩ := hP.universal_ridge_of_count hF hF4 hT hTF hT3 hc hR hRF hR3 hRT
  obtain ⟨hU,hU2⟩ := hP.universal_ridge_of_count hF hF4 hT hTF hT3 hc hS hSF hS3 hST
  by_cases hQ3 : cnt P (T ∩ R) 0 = 3
  · exact ⟨R,hR,hRF,hR3,hr,hQ,hQ2,hQ3⟩
  by_cases hU3 : cnt P (T ∩ S) 0 = 3
  · exact ⟨S,hS,hSF,hS3,hs,hU,hU2,hU3⟩
  have hQ4 : cnt P (T ∩ R) 0 = 4 := by
    have hlo := hP.three_le_cnt hQ hQ2
    have hhi := hP.cnt_zero_lt hQ hR inter_subset_right (by intro he; rw [he,hR3] at hQ2; omega)
    omega
  have hU4 : cnt P (T ∩ S) 0 = 4 := by
    have hlo := hP.three_le_cnt hU hU2
    have hhi := hP.cnt_zero_lt hU hS inter_subset_right (by intro he; rw [he,hS3] at hU2; omega)
    omega
  have hqt := (hP.q4_6117 hT hT3 ht).1
  have heq : T ∩ R = T ∩ S := hP.quad_unique_of_q4_le_one (by omega)
    hQ inter_subset_left hQ2 hQ4 hU inter_subset_left hU2 hU4
  have hQS : T ∩ R ⊆ S := by rw [heq]; exact inter_subset_right
  exact False.elim (hRS (hP.ridge_partner_unique_inside hF hF4 hQ
    (inter_subset_left.trans hTF) hQ2 hT hTF hT3 inter_subset_left
    hR hRF hR3 inter_subset_right hRT hS hSF hS3 hQS hST))

end Kalai5
