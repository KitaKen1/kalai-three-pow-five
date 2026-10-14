import Kalai5.Cube3.OpposedQuadrilateral
import Kalai5.Cube3.QuadrilateralParallelism

/-! At eighteen facets the segment aligns with an edge and with every opposed edge pair. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

def Config.QuadSegmentAlignment (q s : Fin 4) : Prop :=
  ∀ S : SegmentFibre C s,
    (∃ n : E 2,IsEdgeNormal (fibre C.c C.k q) n ∧ ⟪n,S.direction⟫=0) ∧
    ∀ n : E 2,IsEdgeNormal (fibre C.c C.k q) n →
      IsEdgeNormal (fibre C.c C.k q) (-n) → ⟪n,S.direction⟫=0

theorem Config.quadrilateral_alignment {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (τ : Equiv.Perm (Fin 4)) (h0 : (C.cls (τ 0)).card=4)
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1) :
    C.QuadSegmentAlignment (τ 0) (τ 1) := by
  intro S
  have hop (n : E 2) (hn : IsEdgeNormal (fibre C.c C.k (τ 0)) n)
      (hm : IsEdgeNormal (fibre C.c C.k (τ 0)) (-n)) : ⟪n,S.direction⟫=0 := by
    by_contra he
    have hf := C.opposed_quadrilateral_facets hP hrange τ h0 S h2 h3 hn hm he hno
    omega
  refine ⟨?_,hop⟩
  rcases C.quadrilateral_parallelism hP hrange hh τ h0 h2 h3 S with ⟨n,hn,hm⟩ | hparallel
  · exact ⟨n,hn,hop n hn hm⟩
  · exact hparallel

theorem Config.quadrilateral_aligned_pattern {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ τ : Equiv.Perm (Fin 4),(C.cls (τ 0)).card=4 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1 ∧ C.QuadSegmentAlignment (τ 0) (τ 1) := by
  obtain ⟨τ,h0,h1,h2,h3⟩ := C.quadrilateral_segment_pattern hP hrange hh hno
  exact ⟨τ,h0,h1,h2,h3,C.quadrilateral_alignment hP hrange hh hno τ h0 h2 h3⟩

end Kalai5.Cube3
