import Kalai5.Cube3.GenericQuadrilateral
import Kalai5.Cube3.NoTriangleSegments

/-! The remaining quadrilateral must have parallel opposite edges or an edge parallel to the segment. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

def Config.QuadSegmentParallelism (q s : Fin 4) : Prop :=
  ∀ S : SegmentFibre C s,
    (∃ n : E 2,LemmaB.IsEdgeNormal (fibre C.c C.k q) n ∧
      LemmaB.IsEdgeNormal (fibre C.c C.k q) (-n)) ∨
    (∃ n : E 2,LemmaB.IsEdgeNormal (fibre C.c C.k q) n ∧ ⟪n,S.direction⟫=0)

theorem Config.quadrilateral_parallelism {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4)) (h0 : (C.cls (τ 0)).card=4)
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1) :
    C.QuadSegmentParallelism (τ 0) (τ 1) := by
  classical
  intro S
  by_cases hparallel : ∃ n : E 2,LemmaB.IsEdgeNormal (fibre C.c C.k (τ 0)) n ∧
      LemmaB.IsEdgeNormal (fibre C.c C.k (τ 0)) (-n)
  · exact Or.inl hparallel
  right
  by_contra hnone
  obtain ⟨N,hN,hcard⟩ := C.exists_fibre_normals (show 3 ≤ (C.cls (τ 0)).card by omega)
  have hop : ∀ n ∈ N,∀ m ∈ N,n ≠ -m := by
    intro n hn m hm he
    apply hparallel
    exact ⟨m,hN m hm,by rw [← he]; exact hN n hn⟩
  have hsep : ∀ n ∈ N,⟪n,S.direction⟫ ≠ 0 := by
    intro n hn he
    exact hnone ⟨n,hN n hn,he⟩
  have hf := C.generic_quadrilateral_facets hP hrange τ (by omega) S h2 h3 N hN
    (by omega) hop hsep
  omega

theorem Config.quadrilateral_parallel_pattern {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ τ : Equiv.Perm (Fin 4),(C.cls (τ 0)).card=4 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1 ∧ C.QuadSegmentParallelism (τ 0) (τ 1) := by
  obtain ⟨τ,h0,h1,h2,h3⟩ := C.quadrilateral_segment_pattern hP hrange hh hno
  exact ⟨τ,h0,h1,h2,h3,C.quadrilateral_parallelism hP hrange hh τ h0 h2 h3⟩

end Kalai5.Cube3
