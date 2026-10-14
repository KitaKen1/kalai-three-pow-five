import Kalai5.Cube3.BothWidthCount
import Kalai5.Cube3.OpposedIntervals
import Kalai5.Cube3.TwoWidthExceptional

/-! Four ambient vertices on the common normal of two opposite polygon edges. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

namespace TwoWidthSlice
variable (F : TwoWidthSlice C)

lemma both_saturated_coord {z : SlabPoint} (hb : BothWidthSaturated F.ratio F.eta z)
    {j : Fin 4} (hj : j=F.order 2 ∨ j=F.order 3) :
    |F.coords z j|+z.2*F.intervals.radius j=1 := by
  rcases hj with rfl | rfl
  · rw [F.coords_order]
    change |z.1 2|+z.2*F.ratio=1
    simpa only [mul_comm] using hb.1
  · rw [F.coords_order,F.unit,mul_one]
    exact hb.2

theorem opposed_four {j : Fin 4} (hj : j=F.order 2 ∨ j=F.order 3)
    {n : E 2} (hn : IsEdgeNormal (fibre C.c C.k j) n)
    (hm : IsEdgeNormal (fibre C.c C.k j) (-n))
    {a : ℝ} (ha : 0 < a) (he : F.normal=a • n)
    (hlevels : F.intervals.TwoLevels) (hno : ¬ C.ExtraPM) :
    ∃ H : PositiveFamily C (Fin 2 ⊕ Fin 2),∀ i,H.normal i=n := by
  obtain ⟨h0,h2,hm2⟩ := F.eta_not_exceptional hlevels hno
  obtain ⟨G⟩ := doubleSlab_both_four F.ratio_pos F.ratio_le h0 h2 hm2
  obtain ⟨v,w,hv,hw,hvw,hvp,hwp⟩ := F.intervals.upper_pair_of_opposed hn hm ha he
  obtain ⟨p,q,hp,hq,hpq,hpp,hqp⟩ := F.intervals.lower_pair_of_opposed hn hm ha he
  have hmemb (i : Fin 2 ⊕ Fin 2) : F.embed (G.point i) ∈ C.polarModel.extremePoints ℝ := by
    have hs := F.both_saturated_coord (G.both i) hj
    rcases le_total 0 (F.coords (G.point i) j) with hsign | hsign
    · rw [abs_of_nonneg hsign] at hs
      exact F.upper_edge_extreme (G.extreme i) (G.positive i).ne' hv hw hvw hvp hwp hs
    · rw [abs_of_nonpos hsign] at hs
      exact F.lower_edge_extreme (G.extreme i) (G.positive i).ne' hp hq hpq hpp hqp (by linarith)
  have hr (i : Fin 2 ⊕ Fin 2) : ∃ t : ℝ,0 < t ∧ planar (F.embed (G.point i))=t • n := by
    refine ⟨(G.point i).2*a,mul_pos (G.positive i) ha,?_⟩
    rw [F.planar_embed]
    exact (congrArg (fun m : E 2 => (G.point i).2 • m) he).trans (smul_smul _ _ _)
  exact ⟨PositiveFamily.onRay n hn.1 (fun i => F.embed (G.point i))
    (F.embed_injective.comp G.inj) hmemb hr,fun _ => rfl⟩

end TwoWidthSlice
end Kalai5.Cube3
