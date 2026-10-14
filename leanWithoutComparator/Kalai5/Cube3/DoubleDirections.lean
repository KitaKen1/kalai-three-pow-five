import Kalai5.Cube3.DoubleTransfer
import Kalai5.Cube3.NoTriple

/-! Normalize the two remaining widths after choosing a parallel pair. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma det2_self (a : E 2) : det2 a a=0 := by unfold det2; ring

lemma order_pair (i j : Fin 4) (hne : i ≠ j) :
    ∃ τ : Equiv.Perm (Fin 4), τ 0=i ∧ τ 1=j := by
  let τ := Equiv.swap 0 i * Equiv.swap 1 ((Equiv.swap 0 i) j)
  refine ⟨τ,?_,?_⟩
  all_goals
    fin_cases i <;> fin_cases j <;> first | exact (hne rfl).elim | decide

variable {x : Fin 8 → E5} {C : Config x} (S : SegmentData C)

namespace SegmentData

lemma exists_transverse (hno : ¬ C.ExtraPM) (i : Fin 4) :
    ∃ j,det2 (S.direction i) (S.direction j) ≠ 0 := by
  by_contra hh
  push_neg at hh
  obtain ⟨j,hj⟩ := S.not_all_parallel hno
  apply normal2_ne_zero (S.direction_ne_zero i)
  apply orthogonal_two_eq_zero hj
  · rw [normal2_inner]; exact hh 0
  · rw [normal2_inner]; exact hh j

lemma pair_transverse (hno : ¬ C.ExtraPM) (hnt : S.NoTriple) (τ : Equiv.Perm (Fin 4))
    (h01 : det2 (S.direction (τ 0)) (S.direction (τ 1))=0) :
    det2 (S.direction (τ 0)) (S.direction (τ 2)) ≠ 0 ∧
    det2 (S.direction (τ 0)) (S.direction (τ 3)) ≠ 0 := by
  have h23 : det2 (S.direction (τ 0)) (S.direction (τ 2))=0 →
      det2 (S.direction (τ 0)) (S.direction (τ 3))=0 := by
    intro h02
    apply hnt τ
    intro i; fin_cases i
    · exact det2_self _
    · exact h01
    · exact h02
  have h32 : det2 (S.direction (τ 0)) (S.direction (τ 3))=0 →
      det2 (S.direction (τ 0)) (S.direction (τ 2))=0 := by
    intro h03
    have hh := hnt ((Equiv.swap (2 : Fin 4) 3).trans τ)
    simp only [Equiv.trans_apply] at hh
    have hh' := hh (by
      intro i; fin_cases i
      · simpa [Equiv.swap_apply_def] using det2_self (S.direction (τ 0))
      · simpa [Equiv.swap_apply_def] using h01
      · simpa [Equiv.swap_apply_def] using h03)
    simpa [Equiv.swap_apply_def] using hh'
  have hn : ¬(det2 (S.direction (τ 0)) (S.direction (τ 2))=0 ∧
      det2 (S.direction (τ 0)) (S.direction (τ 3))=0) := by
    rintro ⟨h02,h03⟩
    obtain ⟨j,hj⟩ := S.exists_transverse hno (τ 0)
    obtain ⟨j,rfl⟩ := τ.surjective j
    fin_cases j
    · exact hj (det2_self _)
    · exact hj h01
    · exact hj h02
    · exact hj h03
  exact ⟨fun h => hn ⟨h,h23 h⟩,fun h => hn ⟨h32 h,h⟩⟩

theorem doubleFrame_order (τ : Equiv.Perm (Fin 4))
    (h01 : det2 (S.direction (τ 0)) (S.direction (τ 1))=0)
    (h02 : det2 (S.direction (τ 0)) (S.direction (τ 2)) ≠ 0)
    (h03 : det2 (S.direction (τ 0)) (S.direction (τ 3)) ≠ 0)
    (hsmall : |det2 (S.axis (τ 0)) (S.axis (τ 2))| ≤ |det2 (S.axis (τ 0)) (S.axis (τ 3))|) :
    ∃ F : DoubleFrame S,F.order=τ := by
  let n := normal2 (S.axis (τ 0))
  let a := ⟪n,S.axis (τ 2)⟫
  let b := ⟪n,S.axis (τ 3)⟫
  have ha : a ≠ 0 := by dsimp [a,n]; rw [normal2_inner]; exact S.axis_det_ne_zero h02
  have hb : b ≠ 0 := by dsimp [b,n]; rw [normal2_inner]; exact S.axis_det_ne_zero h03
  have hab : |a| ≤ |b| := by simpa [a,b,n,normal2_inner] using hsmall
  have hr : |⟪b⁻¹ • n,S.axis (τ 2)⟫|=|a|/|b| := by
    rw [real_inner_smul_left,abs_mul,abs_inv]
    change |b|⁻¹*|a|=|a|/|b|
    rw [div_eq_mul_inv,mul_comm]
  refine ⟨⟨τ,b⁻¹ • n,?_,?_,?_,?_⟩,rfl⟩
  · intro i; fin_cases i
    · rw [real_inner_smul_left]; change b⁻¹*⟪normal2 (S.axis (τ 0)),S.axis (τ 0)⟫=0
      rw [normal2_orthogonal,mul_zero]
    · rw [real_inner_smul_left]; change b⁻¹*⟪normal2 (S.axis (τ 0)),S.axis (τ 1)⟫=0
      rw [normal2_inner,S.axis_det,h01,mul_zero,mul_zero]
  · rw [real_inner_smul_left]; exact inv_mul_cancel₀ hb
  · rw [hr]; exact div_pos (abs_pos.2 ha) (abs_pos.2 hb)
  · rw [hr]; exact (div_le_one (abs_pos.2 hb)).2 hab

theorem doubleFrame_of_directions (τ : Equiv.Perm (Fin 4))
    (h01 : det2 (S.direction (τ 0)) (S.direction (τ 1))=0)
    (h02 : det2 (S.direction (τ 0)) (S.direction (τ 2)) ≠ 0)
    (h03 : det2 (S.direction (τ 0)) (S.direction (τ 3)) ≠ 0) :
    ∃ F : DoubleFrame S,F.order 0=τ 0 ∧ F.order 1=τ 1 := by
  by_cases hsmall : |det2 (S.axis (τ 0)) (S.axis (τ 2))| ≤ |det2 (S.axis (τ 0)) (S.axis (τ 3))|
  · obtain ⟨F,hF⟩ := S.doubleFrame_order τ h01 h02 h03 hsmall
    exact ⟨F,by rw [hF],by rw [hF]⟩
  · obtain ⟨F,hF⟩ := S.doubleFrame_order ((Equiv.swap (2 : Fin 4) 3).trans τ)
      (by simpa [Equiv.swap_apply_def] using h01) (by simpa [Equiv.swap_apply_def] using h03) (by simpa [Equiv.swap_apply_def] using h02)
      (by simpa [Equiv.swap_apply_def] using (le_of_not_ge hsmall))
    exact ⟨F,by simp [hF,Equiv.swap_apply_def],by simp [hF,Equiv.swap_apply_def]⟩

theorem doubleFrame_of_pair (hno : ¬ C.ExtraPM) (hnt : S.NoTriple)
    {i j : Fin 4} (hij : i ≠ j) (hpar : det2 (S.direction i) (S.direction j)=0) :
    ∃ F : DoubleFrame S,F.order 0=i ∧ F.order 1=j := by
  obtain ⟨τ,h0,h1⟩ := order_pair i j hij
  have h01 : det2 (S.direction (τ 0)) (S.direction (τ 1))=0 := by rwa [h0,h1]
  obtain ⟨h02,h03⟩ := S.pair_transverse hno hnt τ h01
  obtain ⟨F,hF0,hF1⟩ := S.doubleFrame_of_directions τ h01 h02 h03
  exact ⟨F,hF0.trans h0,hF1.trans h1⟩

end SegmentData
end Kalai5.Cube3
