import Kalai5.Cube3.EqualTriangleWidths
import Kalai5.Cube3.TriangleInterpolation

/-! The residual equal-triangle configuration and its interior barycentric weights. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

structure TranslatedTriangleFrame where
  order : Equiv.Perm (Fin 4)
  T : TriangleFibre C (order 2)
  U : TriangleFibre C (order 3)
  single0 : (C.cls (order 0)).card=1
  single1 : (C.cls (order 1)).card=1
  v : Fin 8
  w : Fin 8
  cv : C.c v=order 0
  cw : C.c w=order 1
  pairing : Equiv.Perm (Fin 3)
  normals : ∀ i,T.triangle.normal i=U.triangle.normal (pairing i)
  widths : ∀ i,T.triangle.width i=U.triangle.width (pairing i)
  shift : E 2
  translated : ∀ i,U.triangle.point (pairing i)=T.triangle.point i+shift

namespace TranslatedTriangleFrame
variable {C} (F : TranslatedTriangleFrame C)

noncomputable def anchor : E 2 := (-1/2 : ℝ) • (F.shift+C.signedPoint F.v+C.signedPoint F.w)
noncomputable def beta : Fin 3 → ℝ := F.T.triangle.barycentric F.anchor

lemma height_translation (i : Fin 3) :
    F.U.triangle.height (F.pairing i)=F.T.triangle.height i+⟪F.T.triangle.normal i,F.shift⟫ := by
  obtain ⟨k,l,hkl,hik,hil⟩ := TriangleFibre.edge_points i
  have hσ : F.pairing i ≠ F.pairing k := fun h => hik (F.pairing.injective h)
  have hh := F.U.triangle.normal_eval (F.pairing i) (F.pairing k)
  rw [if_neg hσ,sub_zero,← F.normals,F.translated,inner_add_right,
    F.T.triangle.normal_eval,if_neg hik,sub_zero] at hh
  exact hh.symm

lemma beta_sum : ∑ i,F.beta i=1 := F.T.triangle.barycentric_sum F.anchor

lemma beta_support (i : Fin 3) :
    2*F.T.triangle.width i*F.beta i=F.T.triangle.height i+F.U.triangle.height (F.pairing i)+
      ⟪F.T.triangle.normal i,C.signedPoint F.v+C.signedPoint F.w⟫ := by
  have hw := (F.T.triangle.width_positive i).ne'
  have hh : F.beta i*F.T.triangle.width i=F.T.triangle.height i-⟪F.T.triangle.normal i,F.anchor⟫ :=
    div_mul_cancel₀ _ hw
  rw [anchor,inner_smul_right,inner_add_right,inner_add_right] at hh
  rw [F.height_translation,inner_add_right]
  nlinarith

theorem beta_lt_half {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (i : Fin 3) : F.beta i < 1/2 := by
  have hs := TriangleFibre.shared_support_lt hP hrange hh F.order F.T F.U F.single0 F.single1 hno
    i (F.pairing i) (F.normals i) F.v F.w F.cv F.cw
  rw [← F.widths,min_self,← F.beta_support] at hs
  nlinarith [F.T.triangle.width_positive i]

theorem beta_pos {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (i : Fin 3) : 0 < F.beta i := by
  have h0 := F.beta_lt_half hP hrange hh hno 0
  have h1 := F.beta_lt_half hP hrange hh hno 1
  have h2 := F.beta_lt_half hP hrange hh hno 2
  have hs := F.beta_sum
  rw [Fin.sum_univ_three] at hs
  fin_cases i
  · change 0 < F.beta 0; linarith
  · change 0 < F.beta 1; linarith
  · change 0 < F.beta 2; linarith

theorem balanced_corner {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ f : Fin 3 → ℝ,f 0=1 ∧ f 1= -1 ∧ |f 2|<1 ∧ ∑ i,F.beta i*f i=0 := by
  let t := (F.beta 1-F.beta 0)/F.beta 2
  have ht : |t|<1 := by
    apply abs_lt.2
    have hp := F.beta_pos hP hrange hh hno 2
    have h0 := F.beta_lt_half hP hrange hh hno 0
    have h1 := F.beta_lt_half hP hrange hh hno 1
    have hs := F.beta_sum
    rw [Fin.sum_univ_three] at hs
    constructor
    · apply (lt_div_iff₀ hp).2; linarith
    · apply (div_lt_one hp).2; linarith
  refine ⟨![1,-1,t],rfl,rfl,ht,?_⟩
  have he : t*F.beta 2=F.beta 1-F.beta 0 := div_mul_cancel₀ _ (F.beta_pos hP hrange hh hno 2).ne'
  simp only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  change F.beta 0*1+F.beta 1*(-1)+F.beta 2*t=0
  nlinarith

end TranslatedTriangleFrame
end Kalai5.Cube3
