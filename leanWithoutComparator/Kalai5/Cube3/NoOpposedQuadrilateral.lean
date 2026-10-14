import Kalai5.Cube3.AlignedQuadrilateral

/-! The last quadrilateral has no parallel opposite edges and shares an edge direction with the segment. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

def Config.QuadSegmentNonopposed (q s : Fin 4) : Prop :=
  (∀ n : E 2,IsEdgeNormal (fibre C.c C.k q) n → ¬ IsEdgeNormal (fibre C.c C.k q) (-n)) ∧
    ∀ S : SegmentFibre C s,∃ n : E 2,IsEdgeNormal (fibre C.c C.k q) n ∧ ⟪n,S.direction⟫=0

theorem Config.no_opposed_quadrilateral {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (τ : Equiv.Perm (Fin 4)) (h0 : (C.cls (τ 0)).card=4) (S : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    {n : E 2} (hn : IsEdgeNormal (fibre C.c C.k (τ 0)) n) :
    ¬ IsEdgeNormal (fibre C.c C.k (τ 0)) (-n) := by
  intro hm
  have halign := (C.quadrilateral_alignment hP hrange hh hno τ h0 h2 h3 S).2
  have hf := C.aligned_quadrilateral_facets hP hrange τ h0 S h2 h3 hn hm
    (halign n hn hm) hno halign
  omega

theorem Config.quadrilateral_nonopposed_pattern {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ τ : Equiv.Perm (Fin 4),(C.cls (τ 0)).card=4 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1 ∧ C.QuadSegmentNonopposed (τ 0) (τ 1) := by
  obtain ⟨τ,h0,h1,h2,h3,halign⟩ := C.quadrilateral_aligned_pattern hP hrange hh hno
  obtain ⟨S⟩ := C.segment_fibre h1
  exact ⟨τ,h0,h1,h2,h3,fun n hn => C.no_opposed_quadrilateral hP hrange hh hno τ h0 S h2 h3 hn,
    fun R => (halign R).1⟩

end Kalai5.Cube3
