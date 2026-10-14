import Kalai5.Cube3.SegmentFibre

/-! Two positive widths for a polygon and a transverse segment. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5}

theorem Config.polygon_segment_two_width_slice (C : Config x) (τ : Equiv.Perm (Fin 4))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1)
    (h2 : 3 ≤ (C.cls (τ 2)).card) (S : SegmentFibre C (τ 3))
    (n : E 2) (hn : n ≠ 0) (hSn : ⟪n,S.direction⟫ ≠ 0) :
    ∃ F : TwoWidthSlice C,(F.order=τ ∨ F.order=(Equiv.swap 2 3).trans τ) ∧
      ∃ a : ℝ,0 < a ∧ F.normal=a • n := by
  classical
  obtain ⟨I⟩ := C.projection_intervals n
  have hz0 := I.radius_zero_singleton h0
  have hz1 := I.radius_zero_singleton h1
  have hp2 := I.radius_positive h2 hn
  have hp3 := S.radius_positive I hSn
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

end Kalai5.Cube3
