import Kalai5.Cube3.TriangleSegmentsCount

/-! Exclude the entire (3,2,2,1) distribution; only a quadrilateral, a segment, and two singletons remain. -/
namespace Kalai5.Cube3
open Set FullPrism
variable {x : Fin 8 → E5} (C : Config x)

theorem Config.no_triangle_segments {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (τ : Equiv.Perm (Fin 4)) (h0 : (C.cls (τ 0)).card=3) (h1 : (C.cls (τ 1)).card=2)
    (h2 : (C.cls (τ 2)).card=2) (h3 : (C.cls (τ 3)).card=1) : False := by
  obtain ⟨T⟩ := C.triangle_fibre h0
  obtain ⟨S⟩ := C.segment_fibre h1
  obtain ⟨R⟩ := C.segment_fibre h2
  have hd := C.parallel_triangle_segments hP hrange hh hno τ h0 h3 S R
  have hsep := C.no_shared_triangle_edge hP hrange hh hno τ h0 h3 T S R
  have hf := T.parallel_disjoint_segments_facets hP hrange τ S R h3 hd (fun i => (hsep i).1)
  omega

theorem Config.quadrilateral_segment_pattern {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ τ : Equiv.Perm (Fin 4),(C.cls (τ 0)).card=4 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1 := by
  obtain ⟨τ,h | h⟩ := C.two_size_patterns hP hrange hh hno
  · exact ⟨τ,h⟩
  · exact (C.no_triangle_segments hP hrange hh hno τ h.1 h.2.1 h.2.2.1 h.2.2.2).elim

end Kalai5.Cube3
