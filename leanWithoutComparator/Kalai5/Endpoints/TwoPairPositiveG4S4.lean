import Kalai5.Endpoints.TwoPairPositiveEvent
import Kalai5.Endpoints.TwoPairPositiveG2S10

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def g4s4Multiplicity (R : Row) : ℕ :=
  if R = excRow then 6
  else if R = ⟨7,17,18,8,36⟩ ∨ R = ⟨8,19,19,8,39⟩ ∨ R = ⟨8,20,20,8,39⟩ then 1 else 0

lemma g4s4_expanded : expandRows catalogue g4s4Multiplicity = g4s4Pairs := by
  decide +kernel

lemma g4s4_member : g4s4Pairs ∈ profiles 4 4 := by
  have hm : expandRows catalogue g4s4Multiplicity ∈ searchRows catalogue 9 2 4 :=
    searchRows_complete catalogue g4s4Multiplicity 9 2 4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [g4s4_expanded] at hm
  unfold profiles
  exact List.mem_filter.2 ⟨hm,by decide +kernel⟩

lemma g4s4_length : (profiles 4 4).length = 1 := by
  have h := profile_counts
  simp only [TwoPairPositive.remainingCells_eq,List.map_cons,List.map_nil,
    List.cons.injEq,and_true] at h
  exact h.2.2.2.2.2.2.1

lemma g4s4_unique : profiles 4 4 = [g4s4Pairs] := by
  obtain ⟨l,hl⟩ := List.length_eq_one_iff.1 g4s4_length
  have hm := g4s4_member
  rw [hl,List.mem_singleton] at hm
  rwa [← hm] at hl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_g4s4_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 4) : False := by
  have hm := hP.fewFull18_positive_cell_profile_mem hv hh h1 h6 hlt
  rw [hG,hS,TwoPairPositiveProfile.g4s4_unique,List.mem_singleton] at hm
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [hm] at hp
  exact hP.two_pair_g4s4_profile_false hv hh h1 h6 hlt hS hp

theorem IsCSPolytope5.fewFull18_positive_six_cells
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    ((flagDataOf P).G,(flagDataOf P).Gs) ∈
      [(2,2),(2,4),(2,6),(2,8),(4,2),(4,6)] := by
  have hc := hP.fewFull18_positive_seven_cells hv hh h1 h6 hlt
  have hn : ((flagDataOf P).G,(flagDataOf P).Gs) ≠ ((4,4) : ℤ × ℤ) := by
    intro he
    exact hP.fewFull18_positive_g4s4_false hv hh h1 h6 hlt
      (congrArg Prod.fst he) (congrArg Prod.snd he)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  tauto

end Kalai5
