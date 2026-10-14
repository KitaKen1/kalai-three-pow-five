import Kalai5.Cube3.AlignedDoubleCount
import Kalai5.Cube3.OpposedTriangle

/-! Shared triangle normals with equal orientations give two actual positive vertices. -/

namespace Kalai5.Cube3
open Set
variable {x : Fin 8 → E5} {C : Config x}

theorem TwoWidthSlice.aligned_two (F : TwoWidthSlice C)
    (A : SliceEdge F (F.order 2) 1) (B : SliceEdge F (F.order 3) 1)
    (hlevels : F.intervals.TwoLevels) (hno : ¬ C.ExtraPM)
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C (Fin 2),∀ k,H.normal k=n := by
  obtain ⟨h0,h2,hm2⟩ := F.eta_not_exceptional hlevels hno
  obtain ⟨G⟩ := doubleSlab_aligned_two F.ratio_pos F.ratio_le h0 h2 hm2
  exact F.marked_family G A B hn ha he

theorem TriangleFibre.aligned_two (τ : Equiv.Perm (Fin 4))
    (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM)
    (i j : Fin 3) (he : T.triangle.normal i=U.triangle.normal j) :
    ∃ H : PositiveFamily C (Fin 2),∀ k,H.normal k=T.triangle.normal i := by
  classical
  have hn : T.triangle.normal i ≠ 0 := by
    intro hz; have hu := T.triangle.normal_unit i; rw [hz,norm_zero] at hu; norm_num at hu
  obtain ⟨I⟩ := C.projection_intervals (T.triangle.normal i)
  have hz0 := I.radius_zero_singleton h0
  have hz1 := I.radius_zero_singleton h1
  have hp2 := I.radius_positive (show 3 ≤ (C.cls (τ 2)).card by rw [T.card_class]) hn
  have hp3 := I.radius_positive (show 3 ≤ (C.cls (τ 3)).card by rw [U.card_class]) hn
  by_cases hle : I.radius (τ 2)≤I.radius (τ 3)
  · let F := I.twoWidth τ hz0 hz1 hp2 hp3 hle
    let a := (I.radius (τ 3))⁻¹
    have ha : 0 < a := inv_pos.2 hp3
    have hT : F.normal=a • T.triangle.normal i := rfl
    have hU : F.normal=a • U.triangle.normal j := by rw [hT,he]
    have hl := F.two_levels_of_triangles T U h0 h1 hT hU
    obtain ⟨A⟩ := F.triangle_upper_edge T i ha hT
    obtain ⟨B⟩ := F.triangle_upper_edge U j ha hU
    exact F.aligned_two A B hl hno (T.triangle.normal_unit i) ha hT
  · let σ : Equiv.Perm (Fin 4) := (Equiv.swap 2 3).trans τ
    have hσ0 : σ 0=τ 0 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
    have hσ1 : σ 1=τ 1 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
    have hσ2 : σ 2=τ 3 := by simp [σ]
    have hσ3 : σ 3=τ 2 := by simp [σ]
    have hp3' : 0 < I.radius (σ 3) := by rwa [hσ3]
    let F := I.twoWidth σ (by rwa [hσ0]) (by rwa [hσ1]) (by rwa [hσ2]) hp3'
      (by rw [hσ2,hσ3]; exact (lt_of_not_ge hle).le)
    let a := (I.radius (σ 3))⁻¹
    have ha : 0 < a := inv_pos.2 hp3'
    let T' : TriangleFibre C (σ 3) := T.reclass hσ3.symm
    let U' : TriangleFibre C (σ 2) := U.reclass hσ2.symm
    have hT : F.normal=a • T'.triangle.normal i := rfl
    have hU : F.normal=a • U'.triangle.normal j := by
      change a • T.triangle.normal i=a • U.triangle.normal j
      rw [he]
    have hl := F.two_levels_of_triangles U' T'
      (by change (C.cls (σ 0)).card=1; rwa [hσ0])
      (by change (C.cls (σ 1)).card=1; rwa [hσ1]) hU hT
    obtain ⟨A⟩ := F.triangle_upper_edge U' j ha hU
    obtain ⟨B⟩ := F.triangle_upper_edge T' i ha hT
    exact F.aligned_two A B hl hno (T.triangle.normal_unit i) ha hT

end Kalai5.Cube3
