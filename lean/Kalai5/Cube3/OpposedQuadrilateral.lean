import Kalai5.Cube3.OpposedWidthTransfer
import Kalai5.Cube3.PolygonSegmentSlice
import Kalai5.Cube3.SingleSegmentTransfer

/-! A pair of opposite quadrilateral edges transverse to the segment forces twenty facets. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

theorem Config.opposed_quadrilateral_four (τ : Equiv.Perm (Fin 4))
    (h0 : (C.cls (τ 0)).card=4) (S : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    {n : E 2} (hn : IsEdgeNormal (fibre C.c C.k (τ 0)) n)
    (hm : IsEdgeNormal (fibre C.c C.k (τ 0)) (-n))
    (hSn : ⟪n,S.direction⟫ ≠ 0) (hno : ¬ C.ExtraPM) :
    ∃ H : PositiveFamily C (Fin 2 ⊕ Fin 2),∀ i,H.normal i=n := by
  let σ : Equiv.Perm (Fin 4) :=
    ⟨fun j => ![2,3,0,1] j,fun j => ![2,3,0,1] j,
      by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
  let ρ := σ.trans τ
  have hρ0 : ρ 0=τ 2 := rfl
  have hρ1 : ρ 1=τ 3 := rfl
  have hρ2 : ρ 2=τ 0 := rfl
  have hρ3 : ρ 3=τ 1 := rfl
  obtain ⟨F,horder,a,ha,he⟩ := C.polygon_segment_two_width_slice ρ
    (by rwa [hρ0]) (by rwa [hρ1]) (by rw [hρ2,h0]; omega)
    (S.reclass hρ3.symm) n hn.ne_zero hSn
  have hj : τ 0=F.order 2 ∨ τ 0=F.order 3 := by
    rcases horder with horder | horder
    · left; rw [horder,hρ2]
    · right; rw [horder]; simp [hρ2]
  have hlevels : F.intervals.TwoLevels := by
    intro v
    obtain ⟨k,hk⟩ := τ.surjective (C.c v)
    have hv : C.c v=τ k := hk.symm
    rw [hv]
    fin_cases k
    · exact F.intervals.opposed_quad_two_levels h0 hn hm he v hv
    · exact S.two_levels F.intervals v hv
    · exact F.intervals.singleton_two_levels h2 v hv
    · exact F.intervals.singleton_two_levels h3 v hv
  exact F.opposed_four hj hn hm ha he hlevels hno

theorem Config.opposed_quadrilateral_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (h0 : (C.cls (τ 0)).card=4) (S : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    {n : E 2} (hn : IsEdgeNormal (fibre C.c C.k (τ 0)) n)
    (hm : IsEdgeNormal (fibre C.c C.k (τ 0)) (-n))
    (hSn : ⟪n,S.direction⟫ ≠ 0) (hno : ¬ C.ExtraPM) : 20 ≤ fvec P 4 := by
  obtain ⟨F,hF⟩ := C.opposed_quadrilateral_four τ h0 S h2 h3 hn hm hSn hno
  let σ : Equiv.Perm (Fin 4) :=
    ⟨fun j => ![1,2,3,0] j,fun j => ![3,0,1,2] j,
      by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
  let ρ := σ.trans τ
  have hρ0 : ρ 0=τ 1 := rfl
  have hρ1 : ρ 1=τ 2 := rfl
  have hρ2 : ρ 2=τ 3 := rfl
  have hρ3 : ρ 3=τ 0 := rfl
  obtain ⟨G,hG⟩ := Config.polygon_segment_three ρ (S.reclass hρ0.symm)
    (by rwa [hρ1]) (by rwa [hρ2]) (by rw [hρ3,h0]; omega)
  have hG' : ∀ i,G.normal i=S.normal := hG
  have hne : ∀ i j,F.normal i ≠ G.normal j := by
    intro i j he
    rw [hF,hG'] at he
    exact hSn (by rw [he]; exact S.normal_orthogonal)
  have hop : ∀ i j,F.normal i ≠ -G.normal j := by
    intro i j he
    rw [hF,hG'] at he
    exact hSn (by rw [he,inner_neg_left,S.normal_orthogonal,neg_zero])
  simpa [Fintype.card_sum] using (F.sum G hne hop).facets hP hrange

end Kalai5.Cube3
