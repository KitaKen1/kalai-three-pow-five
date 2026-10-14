import Kalai5.Cube3.SingleZeroSlab
import Kalai5.Cube3.OneWidthConstruction
import Kalai5.Cube3.SegmentFibreRays

/-! A polygon, a segment, and two singletons give three actual vertices on the segment normal. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem OneWidthSlice.single_segment_three (F : OneWidthSlice C) (S : SegmentFibre C (F.order 0))
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C (Fin 3),∀ i,H.normal i=n := by
  obtain ⟨G,hG⟩ := tripleSlab_segment_three F.eta
  have hm (i : Fin 3) : F.embed (G.point i) ∈ C.polarModel.extremePoints ℝ :=
    F.embed_extreme (G.extreme i) (G.positive i).ne'
      (S.first_class.trans S.second_class.symm)
      (fun h => S.distinct (C.signedPoint_inj (S.first_class.trans S.second_class.symm) h.symm))
      (hG i) (F.zero_value _ 0 _ S.first_class) (F.zero_value _ 0 _ S.second_class)
  have hr (i : Fin 3) : ∃ t : ℝ,0 < t ∧ planar (F.embed (G.point i))=t • n := by
    refine ⟨(G.point i).2*a,mul_pos (G.positive i) ha,?_⟩
    rw [F.planar_embed,he,smul_smul]
  exact ⟨PositiveFamily.onRay n hn (fun i => F.embed (G.point i))
    (F.embed_injective.comp G.inj) hm hr,fun _ => rfl⟩

theorem Config.polygon_segment_three (τ : Equiv.Perm (Fin 4))
    (S : SegmentFibre C (τ 0)) (h1 : (C.cls (τ 1)).card=1)
    (h2 : (C.cls (τ 2)).card=1) (h3 : 3 ≤ (C.cls (τ 3)).card) :
    ∃ H : PositiveFamily C (Fin 3),∀ i,H.normal i=S.normal := by
  obtain ⟨I⟩ := C.projection_intervals S.normal
  have hn : S.normal ≠ 0 := by
    intro he; have hh := S.normal_unit; rw [he,norm_zero] at hh; norm_num at hh
  have hp := I.radius_positive h3 hn
  have hz (i : Fin 3) : I.radius (τ i.castSucc)=0 := by
    fin_cases i
    · exact S.radius_zero I S.normal_orthogonal
    · exact I.radius_zero_singleton h1
    · exact I.radius_zero_singleton h2
  let F := I.oneWidth τ hz hp
  exact F.single_segment_three S S.normal_unit (inv_pos.2 hp) rfl

end Kalai5.Cube3
