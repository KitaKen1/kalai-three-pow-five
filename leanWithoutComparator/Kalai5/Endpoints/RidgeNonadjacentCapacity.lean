import Kalai5.Endpoints.RidgePolygonCapacity

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Polygon faces of T account for distinct adjacent ridges. Any collection
of other nonadjacent ridges must fit in the remaining slots of F. -/
theorem IsCSPolytope5.ridge_nonadjacent_capacity
    {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (A : Finset (Set E5))
    (hA : ∀ R ∈ A, R ∈ faces P ∧ R ⊆ F ∧ dim R = 3 ∧ R ≠ T ∧ dim (T ∩ R) ≠ 2) :
    A.card + cnt P T 2 + 1 ≤ cnt P F 3 := by
  have hother : ∀ Q ∈ {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2},
      ∃ R ∈ {R | R ∈ faces P ∧ Q ⊆ R ∧ R ⊆ F ∧ dim R = 3}, R ≠ T := by
    intro Q hQ
    exact exists_ne_of_ncard_eq_two (hP.twoface_in_facet hF h4 hQ.1
      (hQ.2.1.trans hTF) hQ.2.2) ⟨hT,hQ.2.1,hTF,hT3⟩
  choose! f hf hfT using hother
  have hi : Set.InjOn f {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2} := by
    intro Q hQ U hU he
    obtain ⟨hR,hQR,_,hR3⟩ := hf Q hQ
    obtain ⟨hS,hUS,_,hS3⟩ := hf U hU
    have hq := hP.inter_three_eq hQ.1 hQ.2.2 hT hT3 hR hR3 (hfT Q hQ).symm hQ.2.1 hQR
    have hu := hP.inter_three_eq hU.1 hU.2.2 hT hT3 hS hS3 (hfT U hU).symm hU.2.1 hUS
    exact hq.symm.trans ((congrArg (fun R => T ∩ R) he).trans hu)
  let B := f '' {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2}
  have hBfin : B.Finite := (hP.below_finite T 2).image f
  have hBn : B.ncard = cnt P T 2 := hi.ncard_image
  have hTB : T ∉ B := by
    rintro ⟨Q,hQ,he⟩
    exact hfT Q hQ he
  have hd : Disjoint (↑A : Set (Set E5)) (insert T B) := by
    rw [Set.disjoint_left]
    intro R hRA hRB
    obtain ⟨hR,hRF,hR3,hRT,hnd⟩ := hA R hRA
    rcases hRB with he | ⟨Q,hQ,he⟩
    · exact hRT he
    · have hq := hP.inter_three_eq hQ.1 hQ.2.2 hT hT3 hR hR3 hRT.symm
        hQ.2.1 (he ▸ (hf Q hQ).2.1)
      exact hnd (by rw [hq]; exact hQ.2.2)
  have hs : (↑A : Set (Set E5)) ∪ insert T B ⊆ {R | R ∈ faces P ∧ R ⊆ F ∧ dim R = 3} := by
    intro R hR
    rcases hR with hR | rfl | ⟨Q,hQ,rfl⟩
    · exact ⟨(hA R hR).1,(hA R hR).2.1,(hA R hR).2.2.1⟩
    · exact ⟨hT,hTF,hT3⟩
    · exact ⟨(hf Q hQ).1,(hf Q hQ).2.2⟩
  have hc := Set.ncard_le_ncard hs (hP.below_finite F 3)
  rw [Set.ncard_union_eq hd A.finite_toSet (hBfin.insert T),
    Set.ncard_coe_finset,Set.ncard_insert_of_notMem hTB hBfin,hBn] at hc
  exact hc

/-- At most one other ridge can miss T when its polygon count leaves only
one unused slot. -/
theorem IsCSPolytope5.ridge_nonadjacent_unique
    {F T R S : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (hc : cnt P F 3 ≤ cnt P T 2 + 2)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3) (hRT : R ≠ T)
    (hnR : dim (T ∩ R) ≠ 2)
    (hS : S ∈ faces P) (hSF : S ⊆ F) (hS3 : dim S = 3) (hST : S ≠ T)
    (hnS : dim (T ∩ S) ≠ 2) : R = S := by
  by_contra hne
  have ha : ∀ U ∈ ({R,S} : Finset (Set E5)),
      U ∈ faces P ∧ U ⊆ F ∧ dim U = 3 ∧ U ≠ T ∧ dim (T ∩ U) ≠ 2 := by
    intro U hU
    simp only [Finset.mem_insert,Finset.mem_singleton] at hU
    rcases hU with rfl | rfl
    · exact ⟨hR,hRF,hR3,hRT,hnR⟩
    · exact ⟨hS,hSF,hS3,hST,hnS⟩
  have hb := hP.ridge_nonadjacent_capacity hF h4 hT hTF hT3 {R,S} ha
  rw [Finset.card_pair hne] at hb
  omega

end Kalai5

