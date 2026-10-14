import Kalai5.Endpoints.TwoPairPositiveEvent

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Weight three fixes the complete ridge profile of C. The quadrilaterals
in a non-five-vertex ridge cannot also count toward b55. -/
theorem IsCSPolytope5.c_weight_three_profile
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨8,20,20,8,39⟩)
    (hW : q55w P F + 2 * exc P F ≤ 3) :
    q4 P F = 3 ∧ big2 P F = 0 ∧ (b55set P F).ncard = 2 ∧
    tcnt P F (4,6,4) = 2 ∧ tcnt P F (5,8,5) = 5 ∧
    tcnt P F (5,9,6) = 0 ∧ tcnt P F (6,9,5) = 0 ∧
    tcnt P F (6,10,6) = 0 ∧ tcnt P F (6,11,7) = 1 ∧
    tcnt P F (6,12,8) = 0 ∧
    ∀ e p, tcnt P F (7,e,p) = 0 := by
  have hR' := hR
  simp only [faceRow,Row.mk.injEq] at hR'
  obtain ⟨hn,_,hp,hr,hJ⟩ := hR'
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  simp only [hr,hJ,hp] at c1 c2 c3
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num at he
  have hfloor := hP.q55_c_three hF h4 hR
  have hw := hP.q55w_eq_b55 F
  have hbound := hP.q4_add_big_le_exc F
  have hge := hP.q55w_ge F
  have hb0 : big2 P F = 0 := by omega
  have hq := hP.exc_eq_q4_of_big F hb0
  have hq3 : q4 P F = 3 := by omega
  have hb2 : (b55set P F).ncard = 2 := by omega
  have h7 : ∀ e p, tcnt P F (7,e,p) = 0 :=
    hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn (by omega)
  have hpr : tcnt P F (6,9,5) = 0 := by
    have ht := hP.c_weight_five_event_zero hF h4 hR (by omega)
    omega
  have h610 : tcnt P F (6,10,6) = 0 := by
    by_contra hz
    obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (6,10,6))
    simp only [tri3,Prod.mk.injEq] at ht
    have hbt : big2 P T = 0 := by
      have hm := hP.big2_mono_of_subset hTF
      omega
    have het := hP.exc_threeface hT hT3
    rw [ht.2.1,ht.2.2] at het
    have hqt := hP.exc_eq_q4_of_big T hbt
    have hres := hP.b55_add_q4_le hT hTF hT3 (by omega)
    omega
  have hpy := hP.two_b55_le hF h4
  have h7a := h7 11 6
  have h7b := h7 12 7
  have h7c := h7 13 8
  have h7d := h7 14 9
  have h7e := h7 15 10
  have hbi : tcnt P F (5,9,6) = 0 := by
    by_contra hz
    have ht : tcnt P F (4,6,4) = 1 := by omega
    have hb : tcnt P F (5,9,6) = 1 := by omega
    apply hP.not_one_tetrahedron_bipyramid_pyramids hF h4 ht hb
    intro T hT hTF hT3
    have h1 := hP.one_le_tcnt hT hTF hT3
    have hne : T ≠ F := by rintro rfl; omega
    have hlt := hP.cnt_zero_lt hT hF hTF hne
    have hin := hP.tri3_mem_fv8 hT hT3 (by omega)
    simp only [fv8,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h <;>
      rw [h] at h1 ⊢ <;>
      first | (left; rfl) | (right; left; rfl) | (right; right; rfl) | omega
  refine ⟨hq3,hb0,hb2,?_,?_,?_,hpr,h610,?_,?_,h7⟩ <;> omega

end Kalai5
