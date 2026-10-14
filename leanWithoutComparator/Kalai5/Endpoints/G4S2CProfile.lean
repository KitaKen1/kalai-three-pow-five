import Kalai5.Endpoints.RareRowRidges

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.g4s2_C_ridge_types
    (hp : (facetRows P).Perm
      (TwoPairPositiveProfile.g4s2PairsC ++ TwoPairPositiveProfile.g4s2PairsC))
    {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) :
    tri3 P T = (4,6,4) ∨ tri3 P T = (5,8,5) ∨ tri3 P T = (6,9,5) := by
  let A : Set (ℕ × ℕ × ℕ) := {(4,6,4),(5,8,5),(6,9,5)}
  have hc : ((facetRows P).map fun S => if S = (⟨8,20,21,9,42⟩ : Row) then 1 else 0).sum = 2 := by
    rw [(hp.map _).sum_eq]
    decide +kernel
  apply hP.ridge_types_transfer_of_two_row hc A ?_ hF h4 hT hTF hT3
  intro H hH hH4 hne U hU hUH hU3
  have hm : faceRow P H ∈ facetRows P := by
    rw [hP.facetRows_eq]
    exact List.mem_map.2 ⟨H,Finset.mem_toList.2 (by
      rw [Set.Finite.mem_toFinset]; exact ⟨hH,hH4⟩),rfl⟩
  have hr : faceRow P H = excRow ∨ faceRow P H = ⟨7,17,18,8,36⟩ ∨
      faceRow P H = r0Row ∨ faceRow P H = ⟨8,20,21,9,42⟩ := by
    simpa only [TwoPairPositiveProfile.g4s2PairsC,r0Row,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,or_self,or_self_left,or_assoc] using hp.mem_iff.1 hm
  rcases hr with hy | hd | hr | hr
  · exact hP.g4s2_small_ridge_types hH hH4 (Or.inl hy) hU hUH hU3
  · exact hP.g4s2_small_ridge_types hH hH4 (Or.inr hd) hU hUH hU3
  · exact hP.r0_type_cases hH hH4 hr hU hUH hU3
  · exact False.elim (hne hr)

/-- The exceptional row in C has three tetrahedra and six square pyramids.
The flag difference eliminates prisms once all other types are absent. -/
theorem IsCSPolytope5.g4s2_C_Q_profile
    (hp : (facetRows P).Perm
      (TwoPairPositiveProfile.g4s2PairsC ++ TwoPairPositiveProfile.g4s2PairsC))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨8,20,21,9,42⟩) :
    tcnt P F (4,6,4) = 3 ∧ tcnt P F (5,8,5) = 6 ∧
      (∀ T ∈ faces P, T ⊆ F → dim T = 3 →
        tri3 P T = (4,6,4) ∨ tri3 P T = (5,8,5)) := by
  have hz (t : ℕ × ℕ × ℕ) (ht : t ≠ (4,6,4) ∧ t ≠ (5,8,5) ∧ t ≠ (6,9,5)) :
      tcnt P F t = 0 := by
    by_contra hn
    obtain ⟨T,hT,hTF,hT3,he⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F t)
    have hh := hP.g4s2_C_ridge_types hp hF h4 hT hTF hT3
    rw [he] at hh
    tauto
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hp21 : cnt P F 2 = 21 := congrArg Row.p hR
  have hr : cnt P F 3 = 9 := congrArg Row.r hR
  have hj : incid P F 0 3 = 42 := congrArg Row.J hR
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  have z1 := hz (5,9,6) (by decide)
  have z2 := hz (6,10,6) (by decide)
  have z3 := hz (6,11,7) (by decide)
  have z4 := hz (6,12,8) (by decide)
  have z5 := hz (7,11,6) (by decide)
  have z6 := hz (7,12,7) (by decide)
  have z7 := hz (7,13,8) (by decide)
  have z8 := hz (7,14,9) (by decide)
  have z9 := hz (7,15,10) (by decide)
  have zp : tcnt P F (6,9,5) = 0 := by omega
  refine ⟨by omega,by omega,?_⟩
  intro T hT hTF hT3
  rcases hP.g4s2_C_ridge_types hp hF h4 hT hTF hT3 with ht | ht | ht
  · exact Or.inl ht
  · exact Or.inr ht
  · have hl := hP.one_le_tcnt hT hTF hT3
    rw [ht,zp] at hl
    omega

end Kalai5
