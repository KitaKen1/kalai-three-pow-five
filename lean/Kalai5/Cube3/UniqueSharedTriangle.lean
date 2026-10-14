import Kalai5.Cube3.SharedBonusCount
import Kalai5.Cube3.AlignedSupportBonus
import Kalai5.Cube3.TriangleReferenceBonus

/-! A single common oriented edge cannot be the only shared triangle direction. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.second_aligned_direction {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM)
    (i₀ j₀ : Fin 3) (he : T.triangle.normal i₀=U.triangle.normal j₀) :
    ∃ i j,i ≠ i₀ ∧ T.triangle.normal i=U.triangle.normal j := by
  classical
  by_contra hsecond
  have huniq : ∀ i j,T.triangle.normal i=U.triangle.normal j → i=i₀ := by
    intro i j hij
    by_contra hi
    exact hsecond ⟨i,j,hi,hij⟩
  have hop := TriangleFibre.no_opposed_of_eighteen hP hrange hh τ T U h0 h1 hno
  have hnoopp (i : Fin 3) : ¬∃ j,T.triangle.normal i= -U.triangle.normal j := by
    rintro ⟨j,hj⟩; exact hop i j hj
  obtain ⟨v,hv⟩ := C.surj (τ 0)
  obtain ⟨w,hw⟩ := C.surj (τ 1)
  obtain ⟨i,hpos⟩ := T.triangle.exists_positive_support
    (C.signedPoint (U.vertex j₀)+C.signedPoint v+C.signedPoint w)
  by_cases hi : i=i₀
  · subst i
    have hs : ∃ j,T.triangle.Shares U.triangle i₀ j := ⟨j₀,Or.inl he⟩
    have hweight : T.triangle.sharedWeight U.triangle i₀=2 := by
      simp [TriangleData.sharedWeight,hs,hnoopp]
    have hp : ⟪T.triangle.normal i₀,C.signedPoint (U.vertex j₀)⟫=
        U.triangle.height j₀-U.triangle.width j₀ := by
      rw [he,U.evaluation,if_pos rfl]
    have hS : min (T.triangle.width i₀) (U.triangle.width j₀) ≤
        T.triangle.height i₀+U.triangle.height j₀+
          ⟪T.triangle.normal i₀,C.signedPoint v+C.signedPoint w⟫ := by
      rw [inner_add_right,inner_add_right,hp] at hpos
      rw [inner_add_right]
      have hm := min_le_right (T.triangle.width i₀) (U.triangle.width j₀)
      linarith
    obtain ⟨F,hF⟩ := TriangleFibre.aligned_four_of_support τ T U h0 h1 hno i₀ j₀ he v w hv hw hS
    let e : Fin (T.triangle.sharedWeight U.triangle i₀+1) ≃ Fin 2 ⊕ Unit :=
      Fintype.equivOfCardEq (by simp [hweight])
    let G := F.reindex (fun k => selectThree (e k)) (selectThree_injective.comp e.injective)
    exact TriangleFibre.no_matching_bonus hP hrange hh τ T U h0 h1 hno i₀ G
      (fun k => hF (selectThree (e k)))
  · have hs : ¬∃ j,T.triangle.Shares U.triangle i j := by
      rintro ⟨j,hj | hj⟩
      · exact hi (huniq i j hj)
      · exact hop i j hj
    have hweight : T.triangle.sharedWeight U.triangle i=1 := by
      simp [TriangleData.sharedWeight,hs,hnoopp]
    obtain ⟨F,hF⟩ := T.two_positive_of_reference hP hrange τ i v w (U.vertex j₀) hv hw (U.cls j₀) h0 h1 hpos
    let e : Fin (T.triangle.sharedWeight U.triangle i+1) ≃ Fin 2 :=
      Fintype.equivOfCardEq (by simp [hweight])
    exact TriangleFibre.no_matching_bonus hP hrange hh τ T U h0 h1 hno i
      (F.reindex e e.injective) (fun k => hF (e k))

def Config.MultipleAlignedTriangleDirections (C : Config x) (j k : Fin 4) : Prop :=
  ∀ (T : TriangleFibre C j) (U : TriangleFibre C k),
    ∃ a b c d,a ≠ c ∧ T.triangle.normal a=U.triangle.normal b ∧
      T.triangle.normal c=U.triangle.normal d

theorem Config.multiple_aligned_triangle_directions {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (τ : Equiv.Perm (Fin 4)) (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1) :
    C.MultipleAlignedTriangleDirections (τ 0) (τ 1) := by
  classical
  intro T U
  obtain ⟨⟨i,j,hij⟩,hop⟩ := C.aligned_triangle_directions hP hrange hh hno τ h2 h3 T U
  let σ : Equiv.Perm (Fin 4) := ((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans τ
  have hσ0 : σ 0=τ 2 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ1 : σ 1=τ 3 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ2 : σ 2=τ 0 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ3 : σ 3=τ 1 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  let T' : TriangleFibre C (σ 2) := T.reclass hσ2.symm
  let U' : TriangleFibre C (σ 3) := U.reclass hσ3.symm
  obtain ⟨k,l,hki,hkl⟩ := TriangleFibre.second_aligned_direction hP hrange hh σ T' U'
    (by rwa [hσ0]) (by rwa [hσ1]) hno i j hij
  exact ⟨i,j,k,l,Ne.symm hki,hij,hkl⟩

end Kalai5.Cube3
