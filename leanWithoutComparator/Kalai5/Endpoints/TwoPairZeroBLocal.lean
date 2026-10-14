import Kalai5.Endpoints.WeightBFive
import Kalai5.Endpoints.OnePairClosure

/-! Local consequences of the surviving two-pair profile B. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Saturating b55 leaves no quadrilateral in a non-five-vertex ridge. -/
lemma IsCSPolytope5.ridge_quad_le_one_of_b55_eq {F T : Set E5}
    (hb : (b55set P F).ncard = q4 P F)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) : q4 P T ≤ 1 := by
  by_cases hn : cnt P T 0 = 5
  · have hi := hP.tri3_mem_fv8 hT hT3 (by omega)
    simp only [fv8, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
    all_goals
      have hc := congrArg Prod.fst ht
      change cnt P T 0 = _ at hc
      first
      | omega
      | rw [(hP.q4_585 hT hT3 ht).1]
      | rw [(hP.q4_596 hT hT3 ht).1]; omega
  · have := hP.b55_add_q4_le hT hTF hT3 hn
    omega

theorem IsCSPolytope5.two_pair_zero_B_rows
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    faceRow P F = ⟨6,13,13,6,26⟩ ∨ faceRow P F = excRow ∨
      faceRow P F = OnePairProfile.jRow ∨ faceRow P F = OnePairProfile.fullRow 20 ∨
      faceRow P F = OnePairProfile.fullRow 21 := by
  have hm : faceRow P F ∈ facetRows P := by
    rw [hP.facetRows_eq]
    exact List.mem_map.2 ⟨F, Finset.mem_toList.2 (by
      rw [Set.Finite.mem_toFinset]; exact ⟨hF,h4⟩), rfl⟩
  have hin := (hP.two_pair_zero_profileB hv hh hc hG hlt).1.mem_iff.mp hm
  simpa [TwoPairZeroProfile.profileB, OnePairProfile.fullRow, or_assoc] using hin

theorem IsCSPolytope5.two_pair_zero_H_small_ridges
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    {k : ℕ} (hklo : 19 ≤ k) (hkhi : k ≤ 21)
    (hrow : faceRow P F = OnePairProfile.fullRow k) :
    ∀ T ∈ faces P, T ⊆ F → dim T = 3 → q4 P T ≤ 1 := by
  have hb := (hP.two_pair_zero_full_quads hv hh hc hG hlt hF h4 hklo hkhi hrow).2.2.1
  exact fun _ hT hTF hT3 => hP.ridge_quad_le_one_of_b55_eq hb hT hTF hT3

theorem IsCSPolytope5.two_pair_zero_H20_tetra_bounds
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = OnePairProfile.fullRow 20) :
    2 ≤ tcnt P F (4,6,4) ∧ tcnt P F (4,6,4) ≤ 3 := by
  obtain ⟨hq,_,hb,hy,hw⟩ := hP.two_pair_zero_full_quads hv hh hc hG hlt hF h4
    (by omega) (by omega) hrow
  norm_num at hq
  rw [hq] at hb hy hw
  have hrow' := hrow
  simp only [faceRow, OnePairProfile.fullRow, Row.mk.injEq] at hrow'
  obtain ⟨hn,_,hp,hr,hJ⟩ := hrow'
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  have h7 := fun e p => hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn (by omega) e p
  have hprism : tcnt P F (6,9,5) = 0 := by
    by_contra hne
    have := hP.b55_add_three_le_of_prism (by omega : 1 ≤ tcnt P F (6,9,5))
    omega
  simp only [hy,hprism,h7,hr,hJ,hp] at c1 c2 c3
  omega

/-- Every non-Y, non-H20 facet can receive at most one mixed quadrilateral. -/
theorem IsCSPolytope5.two_pair_zero_other_quad_le_one
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hnY : faceRow P F ≠ excRow) (hnH : faceRow P F ≠ OnePairProfile.fullRow 20) :
    q4 P F ≤ 1 := by
  rcases hP.two_pair_zero_B_rows hv hh hc hG hlt hF h4 with h | h | h | h | h
  · have he := hP.exc_eq_faceRow hF h4
    rw [h] at he
    norm_num at he
    have := hP.q4_add_big_le_exc F
    omega
  · exact False.elim (hnY h)
  · exact (hP.J_quad_count hF h4 h).le
  · exact False.elim (hnH h)
  · have he := (hP.two_pair_zero_full_quads hv hh hc hG hlt hF h4
      (by omega) (by omega) h).1
    norm_num at he
    omega

/-- The new profile has the same flag data as the former one-pair profile. -/
theorem IsCSPolytope5.two_pair_zero_B_flagData
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243) :
    flagDataOf P = ⟨16,58,86,60,18,128,270,288,282,450,296,900⟩ := by
  obtain ⟨_,he,hr⟩ := hP.two_pair_zero_profileB hv hh hc hG hlt
  have hS := hP.fewFull18_zero_stress_polar_ten hv hh (by omega) (by omega) hlt hG
  have hI := (hP.zero_stress_eighteen_budgets hv hh hG hS).1
  have hD := hP.flagData_valid
  have hvD : (flagDataOf P).v = 16 := hv
  have hhD : (flagDataOf P).h = 18 := hh
  have heul := hD.euler
  have h03 := hD.f03_eq
  have h13 := hD.f13_eq
  have h14 := hD.f14_eq
  have h024 := hD.f024_eq
  simp only [FlagData.G,FlagData.Gs,hvD,hhD,he,hr,hI] at hG hS heul h03 h13 h14 h024
  rcases hEq : flagDataOf P with ⟨v,e,p,r,h,I,x,y,f03,f13,f14,f024⟩
  simp only [hEq] at hvD hhD he hr hI hG hS heul h03 h13 h14 h024
  congr 1 <;> omega

end Kalai5
