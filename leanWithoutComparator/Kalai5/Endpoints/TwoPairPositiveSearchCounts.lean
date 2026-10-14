import Kalai5.Endpoints.TwoPairPositiveFastSearch

/-! Kernel-checked counts, isolated from the geometric coverage proof. -/
namespace Kalai5.TwoPairPositiveProfile

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem searchRows_length : (searchRows catalogue 9 2 4).length = 1914 := by
  rw [← guardedRows_eq_searchRows]
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem profile_counts :
    (TwoPairPositive.remainingCells.map fun cell => (profiles cell.1 cell.2).length) =
      [42,54,34,14,1,4,1,1] := by
  simp only [profiles_guarded]
  decide +kernel

theorem allProfiles_length : allProfiles.length = 151 := by
  rw [allProfiles,List.length_flatMap,profile_counts]
  rfl

end Kalai5.TwoPairPositiveProfile
