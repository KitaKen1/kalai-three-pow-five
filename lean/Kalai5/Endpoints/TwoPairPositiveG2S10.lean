import Kalai5.Endpoints.TwoPairPositivePrismProfile
import Kalai5.Endpoints.TwoPairPositiveSearchCounts

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def g2s10Multiplicity (R : Row) : ℕ :=
  if R = excRow then 5 else if R = OnePairProfile.jRow then 2
  else if R = OnePairProfile.fullRow 20 ∨ R = ⟨8,20,20,8,39⟩ then 1 else 0

lemma g2s10_expanded : expandRows catalogue g2s10Multiplicity = g2s10Pairs := by
  decide +kernel

lemma g2s10_member : g2s10Pairs ∈ profiles 2 10 := by
  have hm : expandRows catalogue g2s10Multiplicity ∈ searchRows catalogue 9 2 4 :=
    searchRows_complete catalogue g2s10Multiplicity 9 2 4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [g2s10_expanded] at hm
  unfold profiles
  exact List.mem_filter.2 ⟨hm,by decide +kernel⟩

lemma g2s10_length : (profiles 2 10).length = 1 := by
  have h := profile_counts
  simp only [TwoPairPositive.remainingCells_eq,List.map_cons,List.map_nil,
    List.cons.injEq,and_true] at h
  exact h.2.2.2.2.1

lemma g2s10_unique : profiles 2 10 = [g2s10Pairs] := by
  obtain ⟨l,hl⟩ := List.length_eq_one_iff.1 g2s10_length
  have hm := g2s10_member
  rw [hl,List.mem_singleton] at hm
  rwa [← hm] at hl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profiles
      (flagDataOf P).G (flagDataOf P).Gs := by
  have hm := hP.fewFull18_positive_profile_mem hv hh h1 h6 hlt
  unfold TwoPairPositiveProfile.allProfiles at hm
  obtain ⟨⟨G,S⟩,_,hm⟩ := List.mem_flatMap.1 hm
  have hm' := hm
  unfold TwoPairPositiveProfile.profiles at hm'
  have ha := of_decide_eq_true (List.mem_filter.1 hm').2
  obtain ⟨he,hg,_,_⟩ := ha
  obtain ⟨_,_,_,_,he',hg',_,_⟩ := hP.fewFull18_positive_pair_budgets hv hh h1 h6 hlt
  have hG : G = (flagDataOf P).G := by omega
  have hS : S = (flagDataOf P).Gs := by omega
  simpa only [hG,hS] using hm

theorem IsCSPolytope5.fewFull18_positive_g2s10_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 2) (hS : (flagDataOf P).Gs = 10) : False := by
  have hm := hP.fewFull18_positive_cell_profile_mem hv hh h1 h6 hlt
  rw [hG,hS,TwoPairPositiveProfile.g2s10_unique,List.mem_singleton] at hm
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [hm] at hp
  exact hP.two_pair_g2s10_profile_false hv hh h1 h6 hlt hS hp

/-- The prism obstruction removes the (2,10) cell from the eight-cell reduction. -/
theorem IsCSPolytope5.fewFull18_positive_seven_cells
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    ((flagDataOf P).G,(flagDataOf P).Gs) ∈
      [(2,2),(2,4),(2,6),(2,8),(4,2),(4,4),(4,6)] := by
  have hc := (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).2.1
  have hn : ((flagDataOf P).G,(flagDataOf P).Gs) ≠ ((2,10) : ℤ × ℤ) := by
    intro he
    exact hP.fewFull18_positive_g2s10_false hv hh h1 h6 hlt
      (congrArg Prod.fst he) (congrArg Prod.snd he)
  simp only [TwoPairPositive.remainingCells_eq,List.mem_cons,List.not_mem_nil,or_false] at hc
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  tauto

end Kalai5
