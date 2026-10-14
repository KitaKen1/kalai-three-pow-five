import Kalai5.Endpoints.ExactPrismBudget

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Polygon excess is a sum of nonnegative polygon contributions, hence
is monotone under inclusion. -/
theorem IsCSPolytope5.exc_mono_of_subset {T F : Set E5} (hTF : T ⊆ F) :
    exc P T ≤ exc P F := by
  rw [hP.exc_eq_sum T,hP.exc_eq_sum F]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ ⊢
    exact ⟨hQ.1,hQ.2.1.trans hTF,hQ.2.2⟩
  · intro Q hQ _
    rw [Set.Finite.mem_toFinset] at hQ
    have h3 := hP.three_le_cnt hQ.1 hQ.2.2
    omega

/-- A ridge whose polygon excess exceeds that of the whole facet is impossible. -/
theorem IsCSPolytope5.tcnt_zero_of_exc_lt {F : Set E5} {t : ℕ × ℕ × ℕ}
    (he : exc P F < 2 * (t.2.1 : ℤ) - 3 * t.2.2) : tcnt P F t = 0 := by
  by_contra hn
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F t)
  have hl := hP.exc_mono_of_subset hTF
  have hE := hP.exc_threeface hT hT3
  have hte := congrArg (fun u => u.2.1) ht
  have htp := congrArg (fun u => u.2.2) ht
  change cnt P T 1 = t.2.1 at hte
  change cnt P T 2 = t.2.2 at htp
  rw [hte,htp] at hE
  omega

/-- With no polygon larger than a quadrilateral, a (6,10,6) ridge
reserves two quadrilaterals outside b55. -/
theorem IsCSPolytope5.b55_add_two_le_of_6106_no_big {F : Set E5}
    (hb : big2 P F = 0) (ht : 1 ≤ tcnt P F (6,10,6)) :
    (b55set P F).ncard + 2 ≤ q4 P F := by
  obtain ⟨T,hT,hTF,hT3,htype⟩ := hP.exists_of_tcnt ht
  have hbt : big2 P T = 0 := by
    have hm := hP.big2_mono_of_subset hTF
    omega
  have he := hP.exc_threeface hT hT3
  simp only [tri3,Prod.mk.injEq] at htype
  rw [htype.2.1,htype.2.2] at he
  have hqt := hP.exc_eq_q4_of_big T hbt
  have hr := hP.b55_add_q4_le hT hTF hT3 (by omega)
  omega

end Kalai5
