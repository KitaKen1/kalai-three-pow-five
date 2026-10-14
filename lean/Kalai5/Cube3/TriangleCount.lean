import Kalai5.Cube3.TriangleVertices

/-! Four positive vertices per triangle; disjoint triangle directions give 22 facets. -/

namespace Kalai5.Cube3
open Set FullPrism

variable {x : Fin 8 → E5} {C : Config x}

abbrev FourTriangleIndex := Fin 2 ⊕ (Unit ⊕ Unit)

theorem TriangleFibre.four_positive {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 0))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1) :
    ∃ F : PositiveFamily C FourTriangleIndex,∀ k,∃ i,F.normal k=T.triangle.normal i := by
  classical
  obtain ⟨i,F,hF⟩ := T.bonus_positive hP hrange τ h2 h3
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
  refine ⟨F.sum GH hne hop,?_⟩
  rintro (k | (k | k))
  · exact ⟨σ 0,hF' k⟩
  · exact ⟨σ 1,hG k⟩
  · exact ⟨σ 2,hH k⟩

theorem TriangleFibre.two_triangles_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 0)) (U : TriangleFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    (hne : ∀ i j,T.triangle.normal i ≠ U.triangle.normal j)
    (hop : ∀ i j,T.triangle.normal i ≠ -U.triangle.normal j) : 22 ≤ fvec P 4 := by
  classical
  obtain ⟨F,hF⟩ := T.four_positive hP hrange τ h2 h3
  let σ : Equiv.Perm (Fin 4) := (Equiv.swap 0 1).trans τ
  have hσ0 : σ 0=τ 1 := by simp [σ]
  have hσ2 : σ 2=τ 2 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ3 : σ 3=τ 3 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  let U' : TriangleFibre C (σ 0) :=
    ⟨U.vertex,U.inj,fun i => (U.cls i).trans hσ0.symm,
      fun v hv => U.covers v (hv.trans hσ0),U.triangle,U.point_eq⟩
  have hpoint : U'.triangle=U.triangle := rfl
  obtain ⟨G,hG⟩ := U'.four_positive hP hrange σ (by simpa [hσ2] using h2) (by simpa [hσ3] using h3)
  have hne' : ∀ a b,F.normal a ≠ G.normal b := by
    intro a b
    obtain ⟨i,hi⟩ := hF a
    obtain ⟨j,hj⟩ := hG b
    rw [hi,hj,hpoint]; exact hne i j
  have hop' : ∀ a b,F.normal a ≠ -G.normal b := by
    intro a b
    obtain ⟨i,hi⟩ := hF a
    obtain ⟨j,hj⟩ := hG b
    rw [hi,hj,hpoint]; exact hop i j
  have hh := (F.sum G hne' hop').facets hP hrange
  simpa [FourTriangleIndex,Fintype.card_sum] using hh

end Kalai5.Cube3
