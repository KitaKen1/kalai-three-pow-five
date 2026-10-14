import Kalai5.Cube3.OneWidthCount
import Kalai5.Cube3.ParallelTriangleSegments

/-! A triangle and two segments with a common edge normal force at least twenty facets. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.parallel_segments_five (τ : Equiv.Perm (Fin 4))
    (S : SegmentFibre C (τ 0)) (R : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (T : TriangleFibre C (τ 3)) (hno : ¬ C.ExtraPM)
    (i : Fin 3) (hS : ⟪T.triangle.normal i,S.direction⟫=0)
    (hR : ⟪T.triangle.normal i,R.direction⟫=0) :
    ∃ G : PositiveFamily C (Fin 3 ⊕ Fin 2),∀ k,G.normal k=T.triangle.normal i := by
  have hn0 : T.triangle.normal i ≠ 0 := by
    intro he; have hh := T.triangle.normal_unit i; rw [he,norm_zero] at hh; norm_num at hh
  obtain ⟨F,horder,a,ha,hn⟩ := Config.triangle_one_width_slice τ S R h2 T _ hn0 hS hR
  let S' := S.reclass (congrFun (congrArg Equiv.toFun horder) 0).symm
  let R' := R.reclass (congrFun (congrArg Equiv.toFun horder) 1).symm
  have hlevels := F.intervals.parallel_triangle_two_levels τ S R h2 T i hn
  exact F.five_positive S' R' hlevels hno (T.triangle.normal_unit i) ha hn

theorem TriangleFibre.parallel_segments_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ)
    (τ : Equiv.Perm (Fin 4)) (S : SegmentFibre C (τ 0)) (R : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (T : TriangleFibre C (τ 3)) (hno : ¬ C.ExtraPM)
    (i : Fin 3) (hS : ⟪T.triangle.normal i,S.direction⟫=0)
    (hR : ⟪T.triangle.normal i,R.direction⟫=0) : 20 ≤ fvec P 4 := by
  classical
  obtain ⟨F,hF⟩ := TriangleFibre.parallel_segments_five τ S R h2 T hno i hS hR
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  have hσ : σ 0=i := by simp [σ]
  have hn (a b : Fin 3) (hab : a ≠ b) : T.triangle.normal (σ a) ≠ T.triangle.normal (σ b) :=
    fun h => hab (σ.injective (T.triangle.normal_injective h))
  obtain ⟨G,hG⟩ := T.one_positive hP hrange (σ 1)
  obtain ⟨H,hH⟩ := T.one_positive hP hrange (σ 2)
  have hF' : ∀ k,F.normal k=T.triangle.normal (σ 0) := by intro k; rw [hσ]; exact hF k
  let GH := G.sum H
    (fun a b => by rw [hG,hH]; exact hn 1 2 (by decide))
    (fun a b => by rw [hG,hH]; exact T.triangle.no_opposite _ _)
  have hne : ∀ a b,F.normal a ≠ GH.normal b := by
    intro a b; rcases b with b | b
    · change F.normal a ≠ G.normal b
      rw [hF',hG]; exact hn 0 1 (by decide)
    · change F.normal a ≠ H.normal b
      rw [hF',hH]; exact hn 0 2 (by decide)
  have hop : ∀ a b,F.normal a ≠ -GH.normal b := by
    intro a b; rcases b with b | b
    · change F.normal a ≠ -G.normal b
      rw [hF',hG]; exact T.triangle.no_opposite _ _
    · change F.normal a ≠ -H.normal b
      rw [hF',hH]; exact T.triangle.no_opposite _ _
  have hh := (F.sum GH hne hop).facets hP hrange
  simpa [Fintype.card_sum] using hh

end Kalai5.Cube3
