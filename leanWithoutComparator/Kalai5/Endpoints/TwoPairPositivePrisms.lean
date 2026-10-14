import Kalai5.Endpoints.OnePairPrisms

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A triangular-prism ridge raises the C20 weight from three to nine. -/
theorem IsCSPolytope5.c20_prism_weight_nine
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨8,20,20,8,39⟩)
    (ht : 1 ≤ tcnt P F (6,9,5)) :
    q55w P F + 2 * exc P F = 9 := by
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num at he
  have hb := hP.b55_add_three_le_of_prism ht
  have hq := hP.q4_add_big_le_exc F
  have hq3 : q4 P F = 3 := by omega
  have hb0 : (b55set P F).ncard = 0 := by omega
  rw [hP.q55w_eq_b55 F,hq3,hb0,he]
  norm_num

/-- H20 has too little polygon excess to contain a triangular prism. -/
theorem IsCSPolytope5.h20_no_prism
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = OnePairProfile.fullRow 20) :
    tcnt P F (6,9,5) = 0 := by
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num [OnePairProfile.fullRow] at he
  have hq := hP.q4_add_big_le_exc F
  by_contra hn
  have hb := hP.b55_add_three_le_of_prism (by omega : 1 ≤ tcnt P F (6,9,5))
  omega

/-- Each Y contributes exactly one triangular-prism ridge. -/
theorem IsCSPolytope5.Y_prism_count
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = excRow) : tcnt P F (6,9,5) = 1 := by
  obtain ⟨K,hK,hKF,hK3,hKt,hu,_⟩ := hP.Y_prism_base hF h4 hR
  unfold tcnt
  have hs : {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (6,9,5)} = {K} := by
    ext T
    constructor
    · intro hT
      exact Set.mem_singleton_iff.2 (hu T hT.1 hT.2.1 hT.2.2.1 hT.2.2.2)
    · intro hT
      rw [Set.mem_singleton_iff] at hT
      subst T
      exact ⟨hK,hKF,hK3,hKt⟩
  rw [hs,Set.ncard_singleton]

theorem IsCSPolytope5.J_no_prism
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = OnePairProfile.jRow) : tcnt P F (6,9,5) = 0 := by
  unfold tcnt
  have hs : {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (6,9,5)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro T hT
    have ht := hP.J_three_types hF h4 hR T hT.1 hT.2.1 hT.2.2.1
    rw [hT.2.2.2] at ht
    norm_num at ht
  rw [hs,Set.ncard_empty]


end Kalai5
