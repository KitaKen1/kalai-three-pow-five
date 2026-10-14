import Kalai5.Cube3.TriangleBarycentric

/-! Interpolate arbitrary scalar data on the three triangle vertices by an affine function. -/
namespace Kalai5.Cube3.TriangleData
local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma barycentric_point (T : TriangleData) (i k : Fin 3) :
    T.barycentric (T.point k) i=if i=k then 1 else 0 := by
  rw [barycentric,T.normal_eval]
  by_cases hi : i=k
  · rw [if_pos hi,if_pos hi]
    have hw := (T.width_positive i).ne'
    field_simp
    ring
  · simp [hi]

theorem affine_interpolation (T : TriangleData) (f : Fin 3 → ℝ) :
    ∃ a : ℝ,∃ b : E 2,(∀ k,a+⟪b,T.point k⟫=f k) ∧
      ∀ p,a+⟪b,p⟫=∑ i,f i*T.barycentric p i := by
  let a := ∑ i,f i*T.height i/T.width i
  let b := -∑ i,(f i/T.width i) • T.normal i
  have he (p : E 2) : a+⟪b,p⟫=∑ i,f i*T.barycentric p i := by
    simp only [a,b,inner_neg_left,sum_inner,real_inner_smul_left,← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [barycentric]; ring
  refine ⟨a,b,?_,he⟩
  intro k
  rw [he]
  simp [T.barycentric_point]

end Kalai5.Cube3.TriangleData
