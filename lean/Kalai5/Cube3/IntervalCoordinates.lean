import Kalai5.Cube3.ProjectionIntervals

/-! Centered signed offsets for projection intervals, without assuming two-point classes. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x} {n : E 2} (I : ProjectionIntervals C n)

namespace ProjectionIntervals

noncomputable def drift : E 2 →ₗ[ℝ] ℝ where
  toFun b := ∑ j,⟪b,I.center j⟫
  map_add' := by intro a b; simp [inner_add_left,Finset.sum_add_distrib]
  map_smul' := by intro t b; simp [real_inner_smul_left,Finset.mul_sum]

lemma centerEval_sum (p : E5) : ∑ j,I.centerEval p j=I.drift (planar p) := by
  simp_rw [I.centerEval_eq]
  rw [Finset.sum_add_distrib,(balanced_iff_signed_sum _).1 (offsets_balanced p),zero_add]
  rfl

lemma centered_ext {p q : E5} (hp : planar p=planar q) (hu : I.centerEval p=I.centerEval q) : p=q := by
  apply C.evaluation_injective
  funext v
  have he (j : Fin 4) : offsets p j=offsets q j := by
    have h := congrFun hu j
    rw [I.centerEval_eq,I.centerEval_eq,hp] at h
    have hne : balanceSign j ≠ 0 := by
      intro hz; have hh := balanceSign_sq j; rw [hz] at hh; norm_num at hh
    exact mul_left_cancel₀ hne (add_right_cancel h)
  change C.value p v=C.value q v
  rw [Config.value,Config.value,hp,he]

noncomputable def centeredOffset (u : Fin 4 → ℝ) (b : E 2) (j : Fin 4) : ℝ :=
  balanceSign j*(u j-⟪b,I.center j⟫)

lemma centeredOffset_balanced (u : Fin 4 → ℝ) (b : E 2) (hs : ∑ j,u j=I.drift b) :
    Balanced (I.centeredOffset u b) := by
  rw [balanced_iff_signed_sum]
  simp only [centeredOffset,← mul_assoc,balanceSign_sq,one_mul,Finset.sum_sub_distrib]
  exact sub_eq_zero.2 hs

lemma centerEval_pack (u : Fin 4 → ℝ) (b : E 2) (hs : ∑ j,u j=I.drift b) :
    I.centerEval (pack (I.centeredOffset u b) b)=u := by
  funext j
  rw [I.centerEval_eq,offsets_pack (I.centeredOffset_balanced u b hs),planar_pack]
  simp only [centeredOffset,← mul_assoc,balanceSign_sq,one_mul,sub_add_cancel]

end ProjectionIntervals
end Kalai5.Cube3
