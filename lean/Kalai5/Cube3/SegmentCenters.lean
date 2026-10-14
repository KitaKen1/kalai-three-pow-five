import Kalai5.Cube3.SegmentFibre
import Kalai5.Cube3.TriangleSupportIntervals

/-! The projected midpoint of a segment is independent of which endpoints realize the extrema. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x} {j : Fin 4} {n : E 2}
namespace SegmentFibre
variable (S : SegmentFibre C j)

noncomputable def midpoint : E 2 := (1/2 : ℝ) • (C.signedPoint S.first+C.signedPoint S.second)

lemma projected_center (I : ProjectionIntervals C n) : ⟪n,I.center j⟫=⟪n,S.midpoint⟫ := by
  have hl0 := I.lower S.first
  have hl1 := I.lower S.second
  have hu0 := I.upper S.first
  have hu1 := I.upper S.second
  rw [S.first_class] at hl0 hu0
  rw [S.second_class] at hl1 hu1
  rcases S.covers _ (I.clo j) with hlo | hlo <;>
    rcases S.covers _ (I.chi j) with hhi | hhi <;>
    simp only [ProjectionIntervals.center,midpoint,inner_smul_right,inner_add_right,hlo,hhi] at * <;>
    linarith

end SegmentFibre

theorem ProjectionIntervals.triangle_segments_support (τ : Equiv.Perm (Fin 4))
    (T : TriangleFibre C (τ 0)) (S : SegmentFibre C (τ 1)) (R : SegmentFibre C (τ 2))
    (h3 : (C.cls (τ 3)).card=1) (v : Fin 8) (hv : C.c v=τ 3) (i : Fin 3)
    (I : ProjectionIntervals C (T.triangle.normal i)) :
    I.drift (T.triangle.normal i)+I.radius (τ 0)=T.triangle.height i+
      ⟪T.triangle.normal i,S.midpoint+R.midpoint+C.signedPoint v⟫ := by
  have hn : T.triangle.normal i=(1 : ℝ) • T.triangle.normal i := by simp
  change (∑ j,⟪T.triangle.normal i,I.center j⟫)+I.radius (τ 0)=_
  rw [← Equiv.sum_comp τ (fun j => ⟪T.triangle.normal i,I.center j⟫),Fin.sum_univ_four,
    S.projected_center I,R.projected_center I,I.singleton_center h3 v hv,
    I.triangle_center T i (by norm_num : (0 : ℝ)<1) hn,
    I.triangle_radius T i (by norm_num : (0 : ℝ)<1) hn]
  simp only [inner_add_right,one_mul]; ring

end Kalai5.Cube3
