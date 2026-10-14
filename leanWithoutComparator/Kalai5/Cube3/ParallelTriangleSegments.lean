import Kalai5.Cube3.TriangleSegments
import Kalai5.Cube3.NoTriangles

/-! At eighteen facets the two segment fibres in a (3,2,2,1) pattern must be parallel. -/
namespace Kalai5.Cube3
open Set FullPrism
variable {x : Fin 8 → E5} (C : Config x)

def Config.ParallelSegments (j k : Fin 4) : Prop :=
  ∀ (S : SegmentFibre C j) (R : SegmentFibre C k),det2 S.direction R.direction=0

theorem Config.parallel_triangle_segments {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (τ : Equiv.Perm (Fin 4)) (h0 : (C.cls (τ 0)).card=3) (h3 : (C.cls (τ 3)).card=1) :
    C.ParallelSegments (τ 1) (τ 2) := by
  intro S R
  obtain ⟨T⟩ := C.triangle_fibre h0
  let σ : Equiv.Perm (Fin 4) :=
    ⟨fun j => ![1,3,0,2] j,fun j => ![2,0,3,1] j,
      by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
  let ρ := σ.trans τ
  have hρ0 : ρ 0=τ 1 := rfl
  have hρ1 : ρ 1=τ 3 := rfl
  have hρ2 : ρ 2=τ 0 := rfl
  have hρ3 : ρ 3=τ 2 := rfl
  let F : TriangleSegments C := {
    order := ρ
    triangle := T.reclass hρ2.symm
    singleton := by rwa [hρ1]
    segment := fun j => if hj : j=0 then
      S.reclass (by simpa only [if_pos hj] using hρ0.symm)
      else R.reclass (by simpa only [if_neg hj] using hρ3.symm) }
  exact F.parallel_of_eighteen hP hrange hh hno

theorem Config.two_patterns_parallel {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ τ : Equiv.Perm (Fin 4),
    ((C.cls (τ 0)).card=4 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1) ∨
    ((C.cls (τ 0)).card=3 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=2 ∧ (C.cls (τ 3)).card=1 ∧ C.ParallelSegments (τ 1) (τ 2)) := by
  obtain ⟨τ,h | h⟩ := C.two_size_patterns hP hrange hh hno
  · exact ⟨τ,Or.inl h⟩
  · exact ⟨τ,Or.inr ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,
      C.parallel_triangle_segments hP hrange hh hno τ h.1 h.2.2.2⟩⟩

end Kalai5.Cube3
