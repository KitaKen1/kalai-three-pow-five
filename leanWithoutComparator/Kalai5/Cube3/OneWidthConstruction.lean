import Kalai5.Cube3.OneWidthTransfer
import Kalai5.Cube3.SegmentFibre
import Kalai5.Cube3.OpposedTriangle

/-! Normalize the triangle width when both segment projections are constant. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x} {n : E 2}

noncomputable def ProjectionIntervals.oneWidth (I : ProjectionIntervals C n) (τ : Equiv.Perm (Fin 4))
    (hz : ∀ i : Fin 3,I.radius (τ i.castSucc)=0) (hp : 0 < I.radius (τ 3)) :
    OneWidthSlice C where
  normal := (I.radius (τ 3))⁻¹ • n
  intervals := I.scaled (I.radius (τ 3))⁻¹ (inv_nonneg.2 hp.le)
  order := τ
  zero := by intro i; rw [I.radius_scaled,hz,mul_zero]
  unit := by rw [I.radius_scaled,inv_mul_cancel₀ hp.ne']

theorem Config.triangle_one_width_slice (τ : Equiv.Perm (Fin 4))
    (S : SegmentFibre C (τ 0)) (R : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (T : TriangleFibre C (τ 3))
    (n : E 2) (hn : n ≠ 0) (hS : ⟪n,S.direction⟫=0) (hR : ⟪n,R.direction⟫=0) :
    ∃ F : OneWidthSlice C,F.order=τ ∧ ∃ a : ℝ,0 < a ∧ F.normal=a • n := by
  classical
  obtain ⟨I⟩ := C.projection_intervals n
  have hz (i : Fin 3) : I.radius (τ i.castSucc)=0 := by
    fin_cases i
    · exact S.radius_zero I hS
    · exact R.radius_zero I hR
    · exact I.radius_zero_singleton h2
  have hp := I.radius_positive (show 3 ≤ (C.cls (τ 3)).card by rw [T.card_class]) hn
  exact ⟨I.oneWidth τ hz hp,rfl,_,inv_pos.2 hp,rfl⟩

theorem ProjectionIntervals.parallel_triangle_two_levels (I : ProjectionIntervals C n)
    (τ : Equiv.Perm (Fin 4)) (S : SegmentFibre C (τ 0)) (R : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (T : TriangleFibre C (τ 3))
    (i : Fin 3) {a : ℝ} (hn : n=a • T.triangle.normal i) : I.TwoLevels := by
  intro v
  obtain ⟨j,hj⟩ := τ.surjective (C.c v)
  have hv : C.c v=τ j := hj.symm
  rw [hv]
  fin_cases j
  · exact S.two_levels I v hv
  · exact R.two_levels I v hv
  · exact I.singleton_two_levels h2 v hv
  · exact I.triangle_two_levels T i hn v hv

end Kalai5.Cube3
