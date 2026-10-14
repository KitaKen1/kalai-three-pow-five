import Kalai5.Cube3.ParallelTriangleEdge

/-! At eighteen facets, parallel segment fibres cannot share a direction with a triangle edge. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem SegmentFibre.unit_orthogonal_of_parallel {j k : Fin 4}
    (S : SegmentFibre C j) (R : SegmentFibre C k)
    (hd : det2 S.direction R.direction=0) {n : E 2} (hn : ‖n‖=1)
    (hS : ⟪n,S.direction⟫=0) : ⟪n,R.direction⟫=0 := by
  have hR : ⟪S.normal,R.direction⟫=0 := by
    rw [SegmentFibre.normal,real_inner_smul_left,normal2_inner,hd,mul_zero]
  rcases unit_common_orthogonal hn S.normal_unit S.direction_ne_zero hS S.normal_orthogonal with h | h
  · rw [h]; exact hR
  · rw [h,inner_neg_left,hR,neg_zero]

def Config.NoSharedTriangleEdge (t j k : Fin 4) : Prop :=
  ∀ (T : TriangleFibre C t) (S : SegmentFibre C j) (R : SegmentFibre C k) (i : Fin 3),
    ⟪T.triangle.normal i,S.direction⟫ ≠ 0 ∧ ⟪T.triangle.normal i,R.direction⟫ ≠ 0

theorem Config.no_shared_triangle_edge {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (τ : Equiv.Perm (Fin 4)) (h0 : (C.cls (τ 0)).card=3) (h3 : (C.cls (τ 3)).card=1) :
    C.NoSharedTriangleEdge (τ 0) (τ 1) (τ 2) := by
  intro T S R i
  have hd := C.parallel_triangle_segments hP hrange hh hno τ h0 h3 S R
  have hd' : det2 R.direction S.direction=0 := by
    have he : det2 R.direction S.direction= -det2 S.direction R.direction := by
      unfold det2; ring
    rw [he,hd,neg_zero]
  have hbad (hS : ⟪T.triangle.normal i,S.direction⟫=0)
      (hR : ⟪T.triangle.normal i,R.direction⟫=0) : False := by
    let σ : Equiv.Perm (Fin 4) :=
      ⟨fun j => ![1,2,3,0] j,fun j => ![3,0,1,2] j,
        by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
    let ρ := σ.trans τ
    have hρ0 : ρ 0=τ 1 := rfl
    have hρ1 : ρ 1=τ 2 := rfl
    have hρ2 : ρ 2=τ 3 := rfl
    have hρ3 : ρ 3=τ 0 := rfl
    have hf := TriangleFibre.parallel_segments_facets hP hrange ρ
      (S.reclass hρ0.symm) (R.reclass hρ1.symm) (by rwa [hρ2])
      (T.reclass hρ3.symm) hno i hS hR
    omega
  constructor
  · intro hS
    exact hbad hS (S.unit_orthogonal_of_parallel R hd (T.triangle.normal_unit i) hS)
  · intro hR
    exact hbad (R.unit_orthogonal_of_parallel S hd' (T.triangle.normal_unit i) hR) hR

theorem Config.two_patterns_no_shared_edge {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ τ : Equiv.Perm (Fin 4),
    ((C.cls (τ 0)).card=4 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1) ∨
    ((C.cls (τ 0)).card=3 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=2 ∧ (C.cls (τ 3)).card=1 ∧
      C.ParallelSegments (τ 1) (τ 2) ∧ C.NoSharedTriangleEdge (τ 0) (τ 1) (τ 2)) := by
  obtain ⟨τ,h | h⟩ := C.two_patterns_parallel hP hrange hh hno
  · exact ⟨τ,Or.inl h⟩
  · exact ⟨τ,Or.inr ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,
      C.no_shared_triangle_edge hP hrange hh hno τ h.1 h.2.2.2.1⟩⟩

end Kalai5.Cube3
