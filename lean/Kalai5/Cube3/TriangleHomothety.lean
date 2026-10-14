import Kalai5.Cube3.TriangleWidthRatios
import Kalai5.Cube3.TriangleBarycentric

/-! Matching normal directions determine a positive homothety, or a translation at equal widths. -/
namespace Kalai5.Cube3.TriangleData
local notation "⟪" x ", " y "⟫" => inner ℝ x y

theorem homothety_of_widths (T U : TriangleData) (σ : Equiv.Perm (Fin 3))
    (hn : ∀ i,T.normal i=U.normal (σ i)) {a : ℝ}
    (hw : ∀ i,U.width (σ i)=a*T.width i) :
    ∃ d : E 2,∀ k,U.point (σ k)=a • T.point k+d := by
  refine ⟨U.point (σ 0)-a • T.point 0,?_⟩
  intro k
  apply T.normals_separate
  intro i
  have hu (j : Fin 3) : ⟪T.normal i,U.point (σ j)⟫=
      U.height (σ i)-(if i=j then U.width (σ i) else 0) := by
    rw [hn,U.normal_eval]
    simp only [σ.injective.eq_iff]
  rw [inner_add_right,inner_sub_right,inner_smul_right,inner_smul_right,hu,hu,
    T.normal_eval,T.normal_eval,hw]
  split_ifs <;> ring

theorem aligned_homothety (T U : TriangleData) (σ : Equiv.Perm (Fin 3))
    (hn : ∀ i,T.normal i=U.normal (σ i)) :
    ∃ a : ℝ,0 < a ∧ (∀ i,U.width (σ i)=a*T.width i) ∧
      ∃ d : E 2,∀ k,U.point (σ k)=a • T.point k+d := by
  let a := U.width (σ 0)/T.width 0
  have ha : 0 < a := div_pos (U.width_positive _) (T.width_positive _)
  have hw (i : Fin 3) : U.width (σ i)=a*T.width i :=
    (div_eq_iff (T.width_positive i).ne').1 (T.width_ratio_constant U σ hn i 0)
  exact ⟨a,ha,hw,T.homothety_of_widths U σ hn hw⟩

theorem translation_of_widths (T U : TriangleData) (σ : Equiv.Perm (Fin 3))
    (hn : ∀ i,T.normal i=U.normal (σ i)) (hw : ∀ i,T.width i=U.width (σ i)) :
    ∃ d : E 2,∀ k,U.point (σ k)=T.point k+d := by
  obtain ⟨d,hd⟩ := T.homothety_of_widths U σ hn
    (a := 1) (fun i => by rw [one_mul,hw])
  exact ⟨d,fun k => by simpa only [one_smul] using hd k⟩

end Kalai5.Cube3.TriangleData
