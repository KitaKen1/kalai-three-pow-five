import Kalai5.Endpoints.G2S2LastProfile
import Kalai5.Endpoints.FullSixEightCapacity

namespace Kalai5
open Set
open scoped Classical
namespace G2S2
def specialTypes : List (ℕ × ℕ × ℕ) := [(5,9,6),(6,10,6),(6,11,7)]
end G2S2
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.g2s2_last_special_free
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hn : faceRow P F ≠ G2S4.bRow)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ G2S2.specialTypes) : tcnt P F t = 0 := by
  rcases hP.g2s2_last_row_cases hp hF h4 with hY | hD | hB
  · simp only [G2S2.specialTypes,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact hP.bipyr_free_rows_count_zero hF h4 (by rw [hY]; decide +kernel)
    · exact (hP.small_special_free_counts hF h4 (by rw [hY]; decide +kernel)).1
    · exact hP.small_rows_6117_zero hF h4 (by rw [hY]; decide +kernel)
  · simp only [G2S2.specialTypes,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact hP.bipyr_free_rows_count_zero hF h4 (by rw [hD]; decide +kernel)
    · exact (hP.small_special_free_counts hF h4 (by rw [hD]; decide +kernel)).1
    · exact hP.small_rows_6117_zero hF h4 (by rw [hD]; decide +kernel)
  · exact (hn hB).elim

/-- Only the other full pair can receive a wide special ridge, so a B
facet can have at most one ridge among these three types. -/
theorem IsCSPolytope5.g2s2_last_special_le_one
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hB : faceRow P F = G2S4.bRow) :
    tcnt P F (5,9,6) + tcnt P F (6,10,6) + tcnt P F (6,11,7) ≤ 1 := by
  have hn : cnt P F 0 = 8 := congrArg Row.n hB
  have hb := hP.ridge_type_pair_capacity (fun R => R = G2S4.bRow)
    G2S2.specialTypes (by decide +kernel) hp
    (fun H hH hH4 hne t ht => hP.g2s2_last_special_free hp hH hH4 hne t ht) hF h4 hB (by
      intro t ht u hu
      have hm : ∀ t ∈ G2S2.specialTypes, 5 ≤ t.1 := by decide +kernel
      have ht5 := hm t ht
      have hu5 := hm u hu
      omega)
  have hc : (G2S2.lastPairs.filter fun R => decide (R = G2S4.bRow)).length = 2 := by decide +kernel
  simp only [G2S2.specialTypes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hc] at hb
  omega

set_option maxHeartbeats 2000000 in
/-- Face-number arithmetic and the special-ridge capacity leave three
local profiles. No enumeration result is imported into this proof. -/
theorem IsCSPolytope5.g2s2_last_b_cases
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hB : faceRow P F = G2S4.bRow) :
    (fv8.map (tcnt P F) = [3,4,0,0,1,0,0,0,0,0,0,0]) ∨
    (fv8.map (tcnt P F) = [4,2,0,1,0,1,0,0,0,0,0,0]) ∨
    (fv8.map (tcnt P F) = [3,3,1,1,0,0,0,0,0,0,0,0]) := by
  have hn : cnt P F 0 = 8 := congrArg Row.n hB
  have hr : cnt P F 3 = 8 := congrArg Row.r hB
  have hfp : cnt P F 2 = 19 := congrArg Row.p hB
  have hj : incid P F 0 3 = 38 := congrArg Row.J hB
  have h7 : ∀ e p, tcnt P F (7,e,p) = 0 := hP.tcnt_seven_zero_of_sixteen_mod_four hv (by rw [hh]) F
  have a := h7 11 6
  have b := h7 12 7
  have c := h7 13 8
  have d := h7 14 9
  have e := h7 15 10
  have f : tcnt P F (6,12,8) = 0 := hP.tcnt_zero_of_polygon_count hF h4 (by change cnt P F 3 ≤ 8; omega)
  have hcap := hP.g2s2_last_special_le_one hp hF h4 hB
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq,and_true]
  by_cases hpr : tcnt P F (6,9,5) = 0
  · have hs := hP.b_no_prism_special_ridge hF h4 hB hpr
    left
    repeat' constructor <;> omega
  · have hpr1 : tcnt P F (6,9,5) = 1 := by omega
    by_cases hf : tcnt P F (6,11,7) = 1
    · right; left
      repeat' constructor <;> omega
    · right; right
      repeat' constructor <;> omega

/-- Each special ridge is shared by two full B facets. -/
theorem IsCSPolytope5.g2s2_last_special_partner
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs))
    {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hB : faceRow P F = G2S4.bRow)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (ht : tri3 P T ∈ G2S2.specialTypes) :
    ∃ H, H ∈ faces P ∧ dim H = 4 ∧ H ≠ F ∧ H ≠ -F ∧ faceRow P H = G2S4.bRow ∧ T = F ∩ H := by
  obtain ⟨H,hH,hH4,hHF,hTH⟩ := hP.exists_other_facet hT hT3 hTF
  have hHB : faceRow P H = G2S4.bRow := by
    by_contra hn
    have hz := hP.g2s2_last_special_free hp hH hH4 hn _ ht
    have hlo := hP.one_le_tcnt hT hTH hT3
    omega
  have hHnF : H ≠ -F := by
    intro he
    obtain ⟨x,hx⟩ := hT.1
    exact Set.disjoint_left.1 (hP.facet_disjoint_neg hF h4) (hTF hx) (he ▸ hTH hx)
  exact ⟨H,hH,hH4,hHF,hHnF,hHB,hP.three_face_eq_inter hF h4 hH hH4 hHF.symm hT hT3 hTF hTH⟩

end Kalai5
