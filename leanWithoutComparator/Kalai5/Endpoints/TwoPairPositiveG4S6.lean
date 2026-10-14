import Kalai5.Endpoints.TwoPairPositiveG4S2
import Kalai5.Endpoints.CWeightThree

namespace Kalai5
open Set
open scoped Classical

namespace TwoPairPositiveProfile

def g4s6Pairs : List Row :=
  [excRow,excRow,excRow,excRow,excRow,excRow,
   ⟨7,17,18,8,36⟩,⟨8,20,20,8,39⟩,⟨8,20,20,8,39⟩]

lemma g4s6_member : g4s6Pairs ∈ profiles 4 6 :=
  profile_mem_of_count_certificate 4 6 _ (by decide +kernel)

lemma g4s6_length : (profiles 4 6).length = 1 := by
  have h := profile_counts
  simp only [TwoPairPositive.remainingCells_eq,List.map_cons,List.map_nil,
    List.cons.injEq,and_true] at h
  exact h.2.2.2.2.2.2.2

lemma g4s6_unique : profiles 4 6 = [g4s6Pairs] := by
  obtain ⟨l,hl⟩ := List.length_eq_one_iff.1 g4s6_length
  have hm := g4s6_member
  rw [hl,List.mem_singleton] at hm
  rwa [← hm] at hl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_g4s6_profile
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 6) :
    (facetRows P).Perm (TwoPairPositiveProfile.g4s6Pairs ++ TwoPairPositiveProfile.g4s6Pairs) := by
  have hm := hP.fewFull18_positive_cell_profile_mem hv hh h1 h6 hlt
  rw [hG,hS,TwoPairPositiveProfile.g4s6_unique,List.mem_singleton] at hm
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rwa [hm] at hp

/-- In the remaining (4,6) cell all four full facets have the same exact
ridge counts. This is a structural reduction, not an exclusion of the cell. -/
theorem IsCSPolytope5.fewFull18_positive_g4s6_full_profile
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 6)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8) :
    faceRow P F = ⟨8,20,20,8,39⟩ ∧
    q4 P F = 3 ∧ big2 P F = 0 ∧ (b55set P F).ncard = 2 ∧
    tcnt P F (4,6,4) = 2 ∧ tcnt P F (5,8,5) = 5 ∧
    tcnt P F (5,9,6) = 0 ∧ tcnt P F (6,9,5) = 0 ∧
    tcnt P F (6,10,6) = 0 ∧ tcnt P F (6,11,7) = 1 ∧
    tcnt P F (6,12,8) = 0 ∧ ∀ e p, tcnt P F (7,e,p) = 0 := by
  have hp := hP.fewFull18_positive_g4s6_profile hv hh h1 h6 hlt hG hS
  have hm : faceRow P F ∈ facetRows P := by
    rw [hP.facetRows_eq]
    exact List.mem_map.2 ⟨F,Finset.mem_toList.2 (by
      rw [Set.Finite.mem_toFinset]; exact ⟨hF,h4⟩),rfl⟩
  have hm' := hp.mem_iff.1 hm
  have hcases : faceRow P F = excRow ∨ faceRow P F = ⟨7,17,18,8,36⟩ ∨
      faceRow P F = ⟨8,20,20,8,39⟩ := by
    simpa only [TwoPairPositiveProfile.g4s6Pairs,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_self,or_self_left,or_assoc] using hm'
  have hR : faceRow P F = ⟨8,20,20,8,39⟩ := by
    rcases hcases with h | h | h
    · have hn7 : cnt P F 0 = 7 := congrArg Row.n h
      omega
    · have hn7 : cnt P F 0 = 7 := congrArg Row.n h
      omega
    · exact h
  have hsum : (((facetRows P).map q55BSixRowWeight).sum : ℤ) = 120 := by
    rw [(hp.map q55BSixRowWeight).sum_eq]
    decide +kernel
  have hu := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  rw [hS] at hu
  norm_num at hu
  have hw := hP.facet_weight_le_of_row_sum 120 120 hu hsum hF h4
  rw [hR] at hw
  have hwC : q55BSixRowWeight (⟨8,20,20,8,39⟩ : Row) = 3 := by decide +kernel
  rw [hwC] at hw
  exact ⟨hR,hP.c_weight_three_profile hF h4 hR (by omega)⟩

end Kalai5
