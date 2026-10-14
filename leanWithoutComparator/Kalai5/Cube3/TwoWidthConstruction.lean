import Kalai5.Cube3.TwoWidthTransfer

/-! Construct the slice from the actual classes and preserve its oriented normal ray. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x} {n : E 2}

noncomputable def ProjectionIntervals.twoWidth (I : ProjectionIntervals C n) (τ : Equiv.Perm (Fin 4))
    (h0 : I.radius (τ 0)=0) (h1 : I.radius (τ 1)=0)
    (h2 : 0 < I.radius (τ 2)) (h3 : 0 < I.radius (τ 3))
    (hle : I.radius (τ 2)≤I.radius (τ 3)) : TwoWidthSlice C where
  normal := (I.radius (τ 3))⁻¹ • n
  intervals := I.scaled (I.radius (τ 3))⁻¹ (inv_nonneg.2 h3.le)
  order := τ
  zero := by
    intro i
    rw [I.radius_scaled]
    fin_cases i
    · change (I.radius (τ 3))⁻¹*I.radius (τ 0)=0; rw [h0,mul_zero]
    · change (I.radius (τ 3))⁻¹*I.radius (τ 1)=0; rw [h1,mul_zero]
  unit := by rw [I.radius_scaled,inv_mul_cancel₀ h3.ne']
  ratio_pos := by rw [I.radius_scaled]; exact mul_pos (inv_pos.2 h3) h2
  ratio_le := by
    rw [I.radius_scaled,mul_comm]
    exact (div_le_one h3).2 hle

theorem Config.triangle_two_width_slice (C : Config x) (τ : Equiv.Perm (Fin 4))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1)
    (h2 : 3 ≤ (C.cls (τ 2)).card) (h3 : 3 ≤ (C.cls (τ 3)).card)
    (n : E 2) (hn : n ≠ 0) :
    ∃ F : TwoWidthSlice C,(F.order=τ ∨ F.order=(Equiv.swap 2 3).trans τ) ∧
      ∃ a : ℝ,0 < a ∧ F.normal=a • n := by
  classical
  obtain ⟨I⟩ := C.projection_intervals n
  have hz0 := I.radius_zero_singleton h0
  have hz1 := I.radius_zero_singleton h1
  have hp2 := I.radius_positive h2 hn
  have hp3 := I.radius_positive h3 hn
  by_cases hle : I.radius (τ 2)≤I.radius (τ 3)
  · exact ⟨I.twoWidth τ hz0 hz1 hp2 hp3 hle,Or.inl rfl,_,inv_pos.2 hp3,rfl⟩
  · let σ : Equiv.Perm (Fin 4) := (Equiv.swap 2 3).trans τ
    have hσ0 : σ 0=τ 0 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
    have hσ1 : σ 1=τ 1 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
    have hσ2 : σ 2=τ 3 := by simp [σ]
    have hσ3 : σ 3=τ 2 := by simp [σ]
    have hp3' : 0 < I.radius (σ 3) := by rwa [hσ3]
    refine ⟨I.twoWidth σ (by rwa [hσ0]) (by rwa [hσ1]) (by rwa [hσ2]) hp3'
      (by rw [hσ2,hσ3]; exact (lt_of_not_ge hle).le),Or.inr rfl,_,inv_pos.2 hp3',rfl⟩

namespace ProjectionIntervals
variable (I : ProjectionIntervals C n)

def TwoLevels : Prop := ∀ v,
  ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.lo (C.c v))⟫ ∨
  ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.hi (C.c v))⟫

lemma two_levels_of_values {j : Fin 4} {β γ : ℝ}
    (hval : ∀ v,C.c v=j → ⟪n,C.signedPoint v⟫=β ∨ ⟪n,C.signedPoint v⟫=γ)
    (v : Fin 8) (hv : C.c v=j) :
    ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.lo j)⟫ ∨
    ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.hi j)⟫ := by
  have hlo := I.lower v
  have hhi := I.upper v
  rw [hv] at hlo hhi
  rcases hval v hv with hh | hh <;>
    rcases hval (I.lo j) (I.clo j) with hl | hl <;>
    rcases hval (I.hi j) (I.chi j) with hr | hr <;>
    first | left; linarith | right; linarith

lemma triangle_two_levels {j : Fin 4} (T : TriangleFibre C j) (i : Fin 3) {a : ℝ}
    (hn : n=a • T.triangle.normal i) (v : Fin 8) (hv : C.c v=j) :
    ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.lo j)⟫ ∨
    ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.hi j)⟫ := by
  apply I.two_levels_of_values (β := a*(T.triangle.height i-T.triangle.width i))
    (γ := a*T.triangle.height i) _ v hv
  intro w hw
  obtain ⟨k,rfl⟩ := T.covers w hw
  rw [hn,real_inner_smul_left,T.evaluation]
  by_cases he : i=k
  · exact Or.inl (by rw [if_pos he])
  · exact Or.inr (by rw [if_neg he,sub_zero])

lemma singleton_two_levels {j : Fin 4} (h1 : (C.cls j).card=1) (v : Fin 8) (hv : C.c v=j) :
    ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.lo j)⟫ ∨
    ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.hi j)⟫ :=
  Or.inl (congrArg (fun w => ⟪n,C.signedPoint w⟫) (C.eq_of_singleton_class h1 hv (I.clo j)))

end ProjectionIntervals
end Kalai5.Cube3
