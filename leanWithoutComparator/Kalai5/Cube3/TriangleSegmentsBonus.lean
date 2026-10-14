import Kalai5.Cube3.SupportPairVertices
import Kalai5.Cube3.SegmentCenters

/-! Every triangle with two segment classes and a singleton has a positive supporting-edge bonus. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.segments_bonus_positive {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (T : TriangleFibre C (τ 0)) (S : SegmentFibre C (τ 1)) (R : SegmentFibre C (τ 2))
    (h3 : (C.cls (τ 3)).card=1) :
    ∃ i,∃ F : PositiveFamily C (Fin 2),∀ k,F.normal k=T.triangle.normal i := by
  obtain ⟨v,hv⟩ := C.surj (τ 3)
  obtain ⟨i,hi⟩ := T.triangle.exists_positive_support (S.midpoint+R.midpoint+C.signedPoint v)
  obtain ⟨I⟩ := C.projection_intervals (T.triangle.normal i)
  have hp : 0 < I.drift (T.triangle.normal i)+I.radius (τ 0) := by
    rw [I.triangle_segments_support τ T S R h3 v hv i]; exact hi
  have hz : I.radius (τ 3)=0 := I.radius_zero_singleton h3
  by_cases hle : I.radius (τ 2)≤I.radius (τ 1)
  · obtain ⟨F,hF⟩ := T.support_pair_positive hP hrange τ i I hz hle hp
    exact ⟨i,F,hF⟩
  · let σ := (Equiv.swap (1 : Fin 4) 2).trans τ
    have hσ0 : σ 0=τ 0 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
    have hσ1 : σ 1=τ 2 := by simp [σ]
    have hσ2 : σ 2=τ 1 := by simp [σ]
    have hσ3 : σ 3=τ 3 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
    let T' := T.reclass hσ0.symm
    obtain ⟨F,hF⟩ := T'.support_pair_positive hP hrange σ i I (by rwa [hσ3])
      (by rw [hσ2,hσ1]; exact (lt_of_not_ge hle).le) (by
        change 0 < I.drift (T.triangle.normal i)+I.radius (σ 0)
        rwa [hσ0])
    exact ⟨i,F,hF⟩

end Kalai5.Cube3
