import Kalai5.Cube3.TriangleSegmentsBonus
import Kalai5.Cube3.OneWidthBasicCount

/-! Four triangle vertices and three common-normal vertices exclude the remaining parallel configuration. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.segments_four_positive {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 0))
    (S : SegmentFibre C (τ 1)) (R : SegmentFibre C (τ 2))
    (h3 : (C.cls (τ 3)).card=1) :
    ∃ F : PositiveFamily C FourTriangleIndex,∀ k,∃ i,F.normal k=T.triangle.normal i := by
  classical
  obtain ⟨i,F,hF⟩ := T.segments_bonus_positive hP hrange τ S R h3
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

theorem TriangleFibre.parallel_disjoint_segments_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (T : TriangleFibre C (τ 0)) (S : SegmentFibre C (τ 1)) (R : SegmentFibre C (τ 2))
    (h3 : (C.cls (τ 3)).card=1) (hd : det2 S.direction R.direction=0)
    (hsep : ∀ i,⟪T.triangle.normal i,S.direction⟫ ≠ 0) : 20 ≤ fvec P 4 := by
  classical
  obtain ⟨F,hF⟩ := T.segments_four_positive hP hrange τ S R h3
  let σ : Equiv.Perm (Fin 4) :=
    ⟨fun j => ![1,2,3,0] j,fun j => ![3,0,1,2] j,
      by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
  let ρ := σ.trans τ
  have hρ0 : ρ 0=τ 1 := rfl
  have hρ1 : ρ 1=τ 2 := rfl
  have hρ2 : ρ 2=τ 3 := rfl
  have hρ3 : ρ 3=τ 0 := rfl
  obtain ⟨G,hG⟩ := Config.parallel_segments_three ρ (S.reclass hρ0.symm) (R.reclass hρ1.symm)
    (by rwa [hρ2]) (T.reclass hρ3.symm) hd
  have hG' : ∀ k,G.normal k=S.normal := hG
  have hne : ∀ a b,F.normal a ≠ G.normal b := by
    intro a b he
    obtain ⟨i,hi⟩ := hF a
    rw [hi,hG'] at he
    apply hsep i
    rw [he]; exact S.normal_orthogonal
  have hop : ∀ a b,F.normal a ≠ -G.normal b := by
    intro a b he
    obtain ⟨i,hi⟩ := hF a
    rw [hi,hG'] at he
    apply hsep i
    rw [he,inner_neg_left,S.normal_orthogonal,neg_zero]
  have hh := (F.sum G hne hop).facets hP hrange
  simpa [FourTriangleIndex,Fintype.card_sum] using hh

end Kalai5.Cube3
