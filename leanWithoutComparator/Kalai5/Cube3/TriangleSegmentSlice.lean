import Kalai5.Cube3.ZeroCoordinateTransfer
import Kalai5.Cube3.SegmentFibreRays
import Kalai5.Cube3.PositiveSigma
import Kalai5.Cube3.OpposedTriangle

/-! A triangle edge parallel to one of two nonparallel segment fibres gives three vertices. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem Config.mixed_two_width_slice (τ : Equiv.Perm (Fin 4))
    (S : SegmentFibre C (τ 0)) (h1 : (C.cls (τ 1)).card=1)
    (T : TriangleFibre C (τ 2)) (R : SegmentFibre C (τ 3))
    (n : E 2) (hn : n ≠ 0) (hS : ⟪n,S.direction⟫=0) (hR : ⟪n,R.direction⟫ ≠ 0) :
    ∃ F : TwoWidthSlice C,(F.order=τ ∨ F.order=(Equiv.swap 2 3).trans τ) ∧
      ∃ a : ℝ,0 < a ∧ F.normal=a • n := by
  classical
  obtain ⟨I⟩ := C.projection_intervals n
  have hz0 := S.radius_zero I hS
  have hz1 := I.radius_zero_singleton h1
  have hp2 := I.radius_positive (show 3 ≤ (C.cls (τ 2)).card by rw [T.card_class]) hn
  have hp3 := R.radius_positive I hR
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

theorem ProjectionIntervals.mixed_two_levels {n : E 2} (I : ProjectionIntervals C n)
    (τ : Equiv.Perm (Fin 4)) (S : SegmentFibre C (τ 0)) (h1 : (C.cls (τ 1)).card=1)
    (T : TriangleFibre C (τ 2)) (R : SegmentFibre C (τ 3))
    (i : Fin 3) {a : ℝ} (hn : n=a • T.triangle.normal i) : I.TwoLevels := by
  intro v
  obtain ⟨j,hj⟩ := τ.surjective (C.c v)
  have hv : C.c v=τ j := hj.symm
  rw [hv]
  fin_cases j
  · exact S.two_levels I v hv
  · exact I.singleton_two_levels h1 v hv
  · exact I.triangle_two_levels T i hn v hv
  · exact R.two_levels I v hv

theorem TriangleFibre.segment_coincident_three (τ : Equiv.Perm (Fin 4))
    (S : SegmentFibre C (τ 0)) (h1 : (C.cls (τ 1)).card=1)
    (T : TriangleFibre C (τ 2)) (R : SegmentFibre C (τ 3)) (hno : ¬ C.ExtraPM)
    (i : Fin 3) (hS : ⟪T.triangle.normal i,S.direction⟫=0)
    (hR : ⟪T.triangle.normal i,R.direction⟫ ≠ 0) :
    ∃ G : PositiveFamily C (Fin 3),∀ k,G.normal k=T.triangle.normal i := by
  classical
  have hn0 : T.triangle.normal i ≠ 0 := by
    intro he; have hh := T.triangle.normal_unit i; rw [he,norm_zero] at hh; norm_num at hh
  obtain ⟨F,horder,a,ha,hn⟩ := Config.mixed_two_width_slice τ S h1 T R _ hn0 hS hR
  have hF0 : F.order 0=τ 0 := by
    rcases horder with h | h
    · rw [h]
    · rw [h]; norm_num [Equiv.swap_apply_def] <;> decide
  let S' := S.reclass hF0.symm
  have hlevels := F.intervals.mixed_two_levels τ S h1 T R i hn
  obtain ⟨G,hG⟩ := F.zero_three S' hlevels hno (T.triangle.normal_unit i) ha hn
  let e : (Fin 2 ⊕ Unit) ≃ Fin 3 := Fintype.equivFinOfCardEq (by simp)
  exact ⟨G.reindex e.symm e.symm.injective,fun k => hG (e.symm k)⟩

end Kalai5.Cube3
