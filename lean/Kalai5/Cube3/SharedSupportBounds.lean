import Kalai5.Cube3.UniqueSharedTriangle

/-! Necessary support inequalities for any hypothetical eighteen-facet configuration. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.shared_support_lt {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM)
    (i j : Fin 3) (he : T.triangle.normal i=U.triangle.normal j)
    (v w : Fin 8) (hv : C.c v=τ 0) (hw : C.c w=τ 1) :
    T.triangle.height i+U.triangle.height j+⟪T.triangle.normal i,C.signedPoint v+C.signedPoint w⟫ <
      min (T.triangle.width i) (U.triangle.width j) := by
  classical
  by_contra hS
  obtain ⟨F,hF⟩ := TriangleFibre.aligned_four_of_support τ T U h0 h1 hno i j he v w hv hw (le_of_not_gt hS)
  have hop := TriangleFibre.no_opposed_of_eighteen hP hrange hh τ T U h0 h1 hno
  have hnoopp : ¬∃ j,T.triangle.normal i= -U.triangle.normal j := by rintro ⟨j,hj⟩; exact hop i j hj
  have hs : ∃ j,T.triangle.Shares U.triangle i j := ⟨j,Or.inl he⟩
  have hweight : T.triangle.sharedWeight U.triangle i=2 := by simp [TriangleData.sharedWeight,hs,hnoopp]
  let e : Fin (T.triangle.sharedWeight U.triangle i+1) ≃ Fin 2 ⊕ Unit := Fintype.equivOfCardEq (by simp [hweight])
  exact TriangleFibre.no_matching_bonus hP hrange hh τ T U h0 h1 hno i
    (F.reindex (fun k => selectThree (e k)) (selectThree_injective.comp e.injective))
    (fun k => hF (selectThree (e k)))

theorem TriangleFibre.unshared_reference_nonpos {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM)
    (i : Fin 3) (hs : ¬∃ j,T.triangle.normal i=U.triangle.normal j)
    (v w u : Fin 8) (hv : C.c v=τ 0) (hw : C.c w=τ 1) (hu : C.c u=τ 3) :
    T.triangle.height i+⟪T.triangle.normal i,C.signedPoint u+C.signedPoint v+C.signedPoint w⟫ ≤ 0 := by
  classical
  by_contra hn
  obtain ⟨F,hF⟩ := T.two_positive_of_reference hP hrange τ i v w u hv hw hu h0 h1 (lt_of_not_ge hn)
  have hop := TriangleFibre.no_opposed_of_eighteen hP hrange hh τ T U h0 h1 hno
  have hnoopp : ¬∃ j,T.triangle.normal i= -U.triangle.normal j := by rintro ⟨j,hj⟩; exact hop i j hj
  have hshare : ¬∃ j,T.triangle.Shares U.triangle i j := by
    rintro ⟨j,hj | hj⟩; exact hs ⟨j,hj⟩; exact hnoopp ⟨j,hj⟩
  have hweight : T.triangle.sharedWeight U.triangle i=1 := by simp [TriangleData.sharedWeight,hshare,hnoopp]
  let e : Fin (T.triangle.sharedWeight U.triangle i+1) ≃ Fin 2 := Fintype.equivOfCardEq (by simp [hweight])
  exact TriangleFibre.no_matching_bonus hP hrange hh τ T U h0 h1 hno i
    (F.reindex e e.injective) (fun k => hF (e k))

end Kalai5.Cube3
