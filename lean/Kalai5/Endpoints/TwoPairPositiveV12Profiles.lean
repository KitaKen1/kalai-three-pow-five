import Kalai5.Endpoints.WeightVTwelve

namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def profilesV12 (G S : ℤ) : List (List Row) :=
  (profiles G S).filter fun rows => decide (((rows.map q55VTwelveRowWeight).sum : ℤ) ≤ 78 - 3 * S)

def cellsV12 : List (ℤ × ℤ) := [(2,2),(2,4),(2,6),(2,8),(4,2)]

def remainingProfilesV12 : List (List Row) :=
  cellsV12.flatMap fun cell => profilesV12 cell.1 cell.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profileV12_counts :
    (cellsV12.map fun cell => (profilesV12 cell.1 cell.2).length) = [38,49,31,12,2] := by
  simp only [profilesV12,profiles_guarded]
  decide +kernel

theorem remainingProfilesV12_length : remainingProfilesV12.length = 132 := by
  rw [remainingProfilesV12,List.length_flatMap,profileV12_counts]
  rfl

end TwoPairPositiveProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_v12_cell_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.profilesV12 (flagDataOf P).G (flagDataOf P).Gs := by
  exact List.mem_filter.2 ⟨hP.fewFull18_positive_cell_profile_mem hv hh h1 h6 hlt,
    decide_eq_true (hP.fewFull18_positive_vTwelve_pair_budget hv hh h1 h6 hlt)⟩

/-- The geometric weight bound and the proved five-cell reduction leave
exactly the kernel-counted 132-entry list. -/
theorem IsCSPolytope5.fewFull18_positive_v12_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.remainingProfilesV12 := by
  exact List.mem_flatMap.2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    hP.fewFull18_positive_five_cells hv hh h1 h6 hlt,
    hP.fewFull18_positive_v12_cell_profile_mem hv hh h1 h6 hlt⟩

end Kalai5
