import Kalai5.Endpoints.G4S2RareClosure
import Kalai5.Endpoints.G4S2CProfile
import Kalai5.Endpoints.ThreeTetraEdgeObstruction

namespace Kalai5
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.g4s2_C_profile_false
    (hp : (facetRows P).Perm
      (TwoPairPositiveProfile.g4s2PairsC ++ TwoPairPositiveProfile.g4s2PairsC)) : False := by
  have hm : (⟨8,20,21,9,42⟩ : Row) ∈ facetRows P := hp.mem_iff.2 (by decide +kernel)
  obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows hm
  obtain ⟨ht,_,htypes⟩ := hP.g4s2_C_Q_profile hp hF h4 hR
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have he : cnt P F 1 = 20 := congrArg Row.e hR
  have hb := hP.three_tetrahedra_edges_twenty_two hF h4 hn ht htypes
  omega

theorem IsCSPolytope5.fewFull18_positive_g4s2_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 2) : False := by
  have he := hP.fewFull18_positive_g4s2_unique_C hv hh h1 h6 hlt hG hS
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [he] at hp
  exact hP.g4s2_C_profile_false hp

/-- All positive-stress G = 4 cells are closed. -/
theorem IsCSPolytope5.fewFull18_positive_four_cells
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    ((flagDataOf P).G,(flagDataOf P).Gs) ∈ [(2,2),(2,4),(2,6),(2,8)] := by
  have hc := hP.fewFull18_positive_five_cells hv hh h1 h6 hlt
  have hn : ((flagDataOf P).G,(flagDataOf P).Gs) ≠ ((4,2) : ℤ × ℤ) := by
    intro he
    exact hP.fewFull18_positive_g4s2_false hv hh h1 h6 hlt
      (congrArg Prod.fst he) (congrArg Prod.snd he)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  tauto

namespace TwoPairPositiveProfile

def cellsG2 : List (ℤ × ℤ) := [(2,2),(2,4),(2,6),(2,8)]

def remainingProfilesG2 : List (List Row) :=
  cellsG2.flatMap fun cell => profilesV12 cell.1 cell.2

omit hP in
theorem profileG2_counts :
    (cellsG2.map fun cell => (profilesV12 cell.1 cell.2).length) = [38,49,31,12] := by
  have hc := profileV12_counts
  simp only [cellsV12,List.map_cons,List.map_nil,List.cons.injEq,and_true] at hc
  simp only [cellsG2,List.map_cons,List.map_nil,List.cons.injEq,and_true]
  exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1⟩

omit hP in
theorem remainingProfilesG2_length : remainingProfilesG2.length = 130 := by
  rw [remainingProfilesG2,List.length_flatMap,profileG2_counts]
  rfl

end TwoPairPositiveProfile

theorem IsCSPolytope5.fewFull18_positive_g2_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesG2 := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_four_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_v12_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5
