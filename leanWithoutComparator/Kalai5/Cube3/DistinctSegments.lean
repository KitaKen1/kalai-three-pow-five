import Kalai5.Cube3.Segments
import Kalai5.Cube3.CentralVertices

/-! Four nonparallel segment fibres force at least 22 actual facets. -/

namespace Kalai5.Cube3

open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable def sign2 (i : Fin 2) : ℝ := ![1,-1] i

lemma sign2_sign (i : Fin 2) : sign2 i = 1 ∨ sign2 i = -1 := by
  fin_cases i <;> norm_num [sign2]

lemma sign2_ne_zero (i : Fin 2) : sign2 i ≠ 0 := by
  fin_cases i <;> norm_num [sign2]

lemma sign2_injective : Function.Injective sign2 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [sign2] <;> norm_num at h

lemma sign2_eq_of_positive {i j : Fin 2} {a : ℝ}
    (hi : 0 < sign2 i * a) (hj : 0 < sign2 j * a) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [sign2] <;> linarith

variable {x : Fin 8 → E5} {C : Config x} (S : SegmentData C)

namespace SegmentData

theorem four_rays {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) :
    ∃ f : Fin 4 × Fin 2 × Fin 2 → E5,
      (∀ i, f i ∈ C.polarModel.extremePoints ℝ) ∧
      (∀ i v, C.c v = i.1 → C.value (f i) v = sign2 i.2.1) ∧
      ∀ i, 0 < sign2 i.2.2 * ⟪normal2 (S.direction i.1),planar (f i)⟫ := by
  have hex : ∀ i : Fin 4 × Fin 2 × Fin 2, ∃ p ∈ C.polarModel.extremePoints ℝ,
      (∀ v, C.c v = i.1 → C.value p v = sign2 i.2.1) ∧
      0 < sign2 i.2.2 * ⟪normal2 (S.direction i.1),planar p⟫ := by
    intro i
    have hb : sign2 i.2.2 • normal2 (S.direction i.1) ≠ 0 :=
      smul_ne_zero (sign2_ne_zero _) (normal2_ne_zero (S.direction_ne_zero _))
    have hc : ∀ v, C.c v = i.1 →
        ⟪sign2 i.2.2 • normal2 (S.direction i.1),C.k v⟫ =
          sign2 i.2.2 * ⟪normal2 (S.direction i.1),C.k (S.lo i.1)⟫ := by
      intro v hv
      rw [real_inner_smul_left,S.normal_constant _ _ hv]
    obtain ⟨p,hp,hclass,hpos⟩ := C.class_ray_vertex hP hrange i.1 (sign2_sign i.2.1)
      _ hb _ hc
    exact ⟨p,hp,hclass,by simpa only [real_inner_smul_left] using hpos⟩
  choose f hf hclass hpos using hex
  exact ⟨f,hf,hclass,hpos⟩

theorem distinct_directions_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ)
    (hdir : ∀ i j : Fin 4, i ≠ j → det2 (S.direction i) (S.direction j) ≠ 0) :
    22 ≤ fvec P 4 := by
  obtain ⟨f,hf,hclass,hpos⟩ := S.four_rays hP hrange
  have hnz : ∀ i, planar (f i) ≠ 0 := by
    intro i hzero
    have h := hpos i
    rw [hzero,inner_zero_right,mul_zero] at h
    exact (lt_irrefl 0) h
  have hinj : Function.Injective f := by
    intro i j he
    have hij : i.1 = j.1 := by
      by_contra hne
      apply hnz i
      apply orthogonal_two_eq_zero (hdir _ _ hne)
      · exact S.class_orthogonal (hclass i)
      · rw [he]
        exact S.class_orthogonal (hclass j)
    have hs : i.2.1 = j.2.1 := by
      obtain ⟨v,hv⟩ := C.surj i.1
      apply sign2_injective
      rw [← hclass i v hv,he,hclass j v (hv.trans hij)]
    have ht : i.2.2 = j.2.2 := by
      apply sign2_eq_of_positive (hpos i)
      simpa only [← hij,← he] using hpos j
    exact Prod.ext hij (Prod.ext hs ht)
  let g : Fin 6 ⊕ (Fin 4 × Fin 2 × Fin 2) → E5 := Sum.elim centralVertex f
  have hginj : Function.Injective g := by
    intro i j he
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (centralVertex_injective he)
    · have h := congrArg planar he
      exact (hnz j (by simpa [g,centralVertex_planar] using h.symm)).elim
    · have h := congrArg planar he
      exact (hnz i (by simpa [g,centralVertex_planar] using h)).elim
    · exact congrArg Sum.inr (hinj he)
  have hmem : ∀ i, g i ∈ C.polarModel.extremePoints ℝ := by
    rintro (i | i)
    · exact C.centralVertex_extreme i
    · exact hf i
  have h := C.model_vertices_le_facets hP hrange g hginj hmem
  simpa [Fintype.card_sum,Fintype.card_prod] using h

theorem exists_parallel {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) :
    ∃ i j : Fin 4, i ≠ j ∧ det2 (S.direction i) (S.direction j) = 0 := by
  by_contra h
  push_neg at h
  have h22 := S.distinct_directions_facets hP hrange h
  omega

/-- The only unhandled segment arrangements have some parallel classes but
also at least two different directions. -/
def MixedDirections : Prop :=
  (∃ i j : Fin 4, i ≠ j ∧ det2 (S.direction i) (S.direction j) = 0) ∧
  ∃ j : Fin 4, det2 (S.direction 0) (S.direction j) ≠ 0

theorem mixed_directions {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (hno : ¬ C.ExtraPM) : S.MixedDirections :=
  ⟨S.exists_parallel hP hrange hh,S.not_all_parallel hno⟩

end SegmentData

theorem Config.segments_mixed {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (hno : ¬ C.ExtraPM) (hsize : ∀ j, (C.cls j).card = 2) :
    ∃ S : SegmentData C, S.MixedDirections := by
  obtain ⟨S⟩ := C.segments_of_size_two hsize
  exact ⟨S,S.mixed_directions hP hrange hh hno⟩

end Kalai5.Cube3
