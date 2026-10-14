import Kalai5.Cube3.TriangleSegmentSlice
import Kalai5.Cube3.MixedDirectionCount

/-! Exclude two nonparallel segment fibres in the (3,2,2,1) distribution. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

structure TriangleSegments where
  order : Equiv.Perm (Fin 4)
  triangle : TriangleFibre C (order 2)
  singleton : (C.cls (order 1)).card=1
  segment : ∀ j : Fin 2,SegmentFibre C (order (if j=0 then 0 else 3))

namespace TriangleSegments
variable {C} (F : TriangleSegments C)

noncomputable def directions (hd : det2 (F.segment 0).direction (F.segment 1).direction ≠ 0) :
    MixedDirections F.triangle.triangle where
  direction j := (F.segment j).direction
  nonzero j := (F.segment j).direction_ne_zero
  transverse := hd

theorem shared_three (hno : ¬ C.ExtraPM)
    (hd : det2 (F.segment 0).direction (F.segment 1).direction ≠ 0)
    (i : Fin 3) (j : Fin 2) (hj : ⟪F.triangle.triangle.normal i,(F.segment j).direction⟫=0) :
    ∃ G : PositiveFamily C (Fin 3),∀ k,G.normal k=F.triangle.triangle.normal i := by
  have hbad (h0 : ⟪F.triangle.triangle.normal i,(F.segment 0).direction⟫=0)
      (h1 : ⟪F.triangle.triangle.normal i,(F.segment 1).direction⟫=0) : False := by
    have hz := orthogonal_two_eq_zero hd h0 h1
    have hu := F.triangle.triangle.normal_unit i
    rw [hz,norm_zero] at hu; norm_num at hu
  fin_cases j
  · change ⟪F.triangle.triangle.normal i,(F.segment 0).direction⟫=0 at hj
    exact TriangleFibre.segment_coincident_three F.order (F.segment 0) F.singleton F.triangle
      (F.segment 1) hno i hj (hbad hj)
  · change ⟪F.triangle.triangle.normal i,(F.segment 1).direction⟫=0 at hj
    let τ := (Equiv.swap (0 : Fin 4) 3).trans F.order
    have hτ0 : τ 0=F.order 3 := by simp [τ]
    have hτ1 : τ 1=F.order 1 := by norm_num [τ,Equiv.swap_apply_def] <;> decide
    have hτ2 : τ 2=F.order 2 := by norm_num [τ,Equiv.swap_apply_def] <;> decide
    have hτ3 : τ 3=F.order 0 := by simp [τ]
    exact TriangleFibre.segment_coincident_three τ ((F.segment 1).reclass hτ0.symm)
      (by rw [hτ1]; exact F.singleton) (F.triangle.reclass hτ2.symm) ((F.segment 0).reclass hτ3.symm)
      hno i hj (fun h => hbad h hj)

theorem nonparallel_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hno : ¬ C.ExtraPM)
    (hd : det2 (F.segment 0).direction (F.segment 1).direction ≠ 0) : 20 ≤ fvec P 4 := by
  classical
  let D := F.directions hd
  have hfamily (i : Fin 3) : ∃ G : PositiveFamily C (Fin (D.weight i)),
      ∀ k,G.normal k=F.triangle.triangle.normal i := by
    by_cases hs : ∃ j,D.Shares i j
    · have hw : D.weight i=3 := by simp [MixedDirections.weight,hs]
      obtain ⟨j,hj⟩ := hs
      obtain ⟨G,hG⟩ := F.shared_three hno hd i j hj
      let e : Fin (D.weight i) ≃ Fin 3 := Fintype.equivOfCardEq (by simp [hw])
      exact ⟨G.reindex e e.injective,fun k => hG (e k)⟩
    · have hw : D.weight i=1 := by simp [MixedDirections.weight,hs]
      obtain ⟨G,hG⟩ := F.triangle.one_positive hP hrange i
      let e : Fin (D.weight i) ≃ Unit := Fintype.equivOfCardEq (by simp [hw])
      exact ⟨G.reindex e e.injective,fun k => hG (e k)⟩
  choose G hG using hfamily
  have hsegments (j : Fin 2) : ∃ H : PositiveFamily C (Fin 2),
      ∀ k,H.normal k=(F.segment j).normal :=
    (F.segment j).two_positive hP hrange (F.segment j).normal_unit (F.segment j).normal_orthogonal
  choose H hH using hsegments
  exact D.weighted_facets hP hrange G hG (fun j => (F.segment j).normal)
    (fun j => (F.segment j).normal_unit) (fun j => (F.segment j).normal_orthogonal) H hH

theorem parallel_of_eighteen {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    det2 (F.segment 0).direction (F.segment 1).direction=0 := by
  by_contra hd
  have hf := F.nonparallel_facets hP hrange hno hd
  omega

end TriangleSegments
end Kalai5.Cube3
