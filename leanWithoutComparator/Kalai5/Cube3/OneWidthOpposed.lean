import Kalai5.Cube3.SlabWidthSaturation
import Kalai5.Cube3.OpposedIntervals
import Kalai5.Cube3.OneWidthExceptional
import Kalai5.Cube3.PositiveFamilies

/-! A polygon with two opposed support edges lifts every one-width slab vertex. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}
namespace OneWidthSlice
variable (F : OneWidthSlice C)

theorem upper_edge_extreme {z : SlabPoint}
    (hz : z ∈ (tripleSlab F.eta).extremePoints ℝ) (ht : z.2 ≠ 0)
    {j : Fin 4} {v w : Fin 8} (hv : C.c v=j) (hw : C.c w=j)
    (hneq : C.signedPoint w ≠ C.signedPoint v)
    (hvp : ⟪F.normal,C.signedPoint v⟫=⟪F.normal,C.signedPoint (F.intervals.hi j)⟫)
    (hwp : ⟪F.normal,C.signedPoint w⟫=⟪F.normal,C.signedPoint (F.intervals.hi j)⟫)
    (hsat : F.coords z j+z.2*F.intervals.radius j=1) :
    F.embed z ∈ C.polarModel.extremePoints ℝ :=
  F.embed_extreme hz ht (hv.trans hw.symm) hneq (Or.inl rfl)
    ((F.signed_eq_hi z hv hvp).trans hsat) ((F.signed_eq_hi z hw hwp).trans hsat)

theorem lower_edge_extreme {z : SlabPoint}
    (hz : z ∈ (tripleSlab F.eta).extremePoints ℝ) (ht : z.2 ≠ 0)
    {j : Fin 4} {v w : Fin 8} (hv : C.c v=j) (hw : C.c w=j)
    (hneq : C.signedPoint w ≠ C.signedPoint v)
    (hvp : ⟪F.normal,C.signedPoint v⟫=⟪F.normal,C.signedPoint (F.intervals.lo j)⟫)
    (hwp : ⟪F.normal,C.signedPoint w⟫=⟪F.normal,C.signedPoint (F.intervals.lo j)⟫)
    (hsat : F.coords z j-z.2*F.intervals.radius j= -1) :
    F.embed z ∈ C.polarModel.extremePoints ℝ :=
  F.embed_extreme hz ht (hv.trans hw.symm) hneq (Or.inr rfl)
    ((F.signed_eq_lo z hv hvp).trans hsat) ((F.signed_eq_lo z hw hwp).trans hsat)

theorem opposed_family {n : E 2}
    (hn : IsEdgeNormal (fibre C.c C.k (F.order 3)) n)
    (hm : IsEdgeNormal (fibre C.c C.k (F.order 3)) (-n))
    {a : ℝ} (ha : 0 < a) (he : F.normal=a • n)
    {ι : Type*} (G : SlabFamily F.eta ι) :
    ∃ H : PositiveFamily C ι,∀ i,H.normal i=n := by
  obtain ⟨v,w,hv,hw,hvw,hvp,hwp⟩ := F.intervals.upper_pair_of_opposed hn hm ha he
  obtain ⟨p,q,hp,hq,hpq,hpp,hqp⟩ := F.intervals.lower_pair_of_opposed hn hm ha he
  have hmemb (i : ι) : F.embed (G.point i) ∈ C.polarModel.extremePoints ℝ := by
    have hs : |F.coords (G.point i) (F.order 3)|+(G.point i).2*F.intervals.radius (F.order 3)=1 := by
      rw [F.coords_order,F.unit,mul_one]
      exact tripleSlab_positive_width_saturated (G.extreme i) (G.positive i).le
    rcases le_total 0 (F.coords (G.point i) (F.order 3)) with hsign | hsign
    · rw [abs_of_nonneg hsign] at hs
      exact F.upper_edge_extreme (G.extreme i) (G.positive i).ne' hv hw hvw hvp hwp hs
    · rw [abs_of_nonpos hsign] at hs
      exact F.lower_edge_extreme (G.extreme i) (G.positive i).ne' hp hq hpq hpp hqp (by linarith)
  have hr (i : ι) : ∃ t : ℝ,0 < t ∧ planar (F.embed (G.point i))=t • n := by
    refine ⟨(G.point i).2*a,mul_pos (G.positive i) ha,?_⟩
    rw [F.planar_embed]
    exact (congrArg (fun m : E 2 => (G.point i).2 • m) he).trans (smul_smul _ _ _)
  exact ⟨PositiveFamily.onRay n hn.1 (fun i => F.embed (G.point i))
    (F.embed_injective.comp G.inj) hmemb hr,fun _ => rfl⟩

theorem opposed_five {n : E 2}
    (hn : IsEdgeNormal (fibre C.c C.k (F.order 3)) n)
    (hm : IsEdgeNormal (fibre C.c C.k (F.order 3)) (-n))
    {a : ℝ} (ha : 0 < a) (he : F.normal=a • n)
    (hlevels : F.intervals.TwoLevels) (hno : ¬ C.ExtraPM) :
    ∃ H : PositiveFamily C (Fin 3 ⊕ Fin 2),∀ i,H.normal i=n := by
  obtain ⟨h1,hm1,h3,hm3⟩ := F.eta_not_exceptional hlevels hno
  obtain ⟨G⟩ := tripleSlab_five h1 hm1 h3 hm3
  exact F.opposed_family hn hm ha he G

end OneWidthSlice
end Kalai5.Cube3
