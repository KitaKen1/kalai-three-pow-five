import Kalai5.FullPrism.Structure

/-!
# The full combinatorial structure of a facet `Δ1 × Δ3`

`prism_structure`: a 4-polytope `K = conv VF` (with `VF` its vertex set) whose row is `tRow` has
vertices `x s k` (`s < 2`, `k < 4`) and facets `R i` (the two tetrahedra) and `C j` (the four
triangular prisms) with `x s k ∈ R i ↔ s ≠ i` and `x s k ∈ C j ↔ k ≠ j`.

From `prism_sides` (the four sides `S k` and the pairs `v_{2k}, v_{2k+1}` they miss): the other two
facets `T, T'` share the vertices (each vertex lies in four facets, three of them sides), and each
meets every pair (a facet missing a pair lies in the corresponding side, hence equals it).

`IsCSPolytope5.prism_facet`: the same for a facet of a centrally symmetric 5-polytope.
-/

namespace Kalai5

open Set FullPrism

variable {d : ℕ}

section

open Classical

variable {VF : Finset (E d)}

section prism

variable (hext : (VF : Set (E d)) = (convexHull ℝ (VF : Set (E d))).extremePoints ℝ)
  (h4 : dim (convexHull ℝ (VF : Set (E d))) = 4)
  (hrow : rowOf (convexHull ℝ (VF : Set (E d))) = tRow)
include hext h4 hrow

/-- **The structure of `Δ1 × Δ3`**: two tetrahedra `R i` and four prisms `C j`. -/
theorem prism_structure : ∃ (x : Fin 2 → Fin 4 → E d) (R : Fin 2 → Set (E d))
    (C : Fin 4 → Set (E d)),
    (∀ s k s' k', x s k = x s' k' → s = s' ∧ k = k') ∧
    (∀ s k, x s k ∈ VF) ∧ (∀ y ∈ VF, ∃ s k, y = x s k) ∧
    (∀ i, R i ∈ faces (convexHull ℝ (VF : Set (E d))) ∧ dim (R i) = 3) ∧
    (∀ j, C j ∈ faces (convexHull ℝ (VF : Set (E d))) ∧ dim (C j) = 3) ∧
    (∀ s k i, x s k ∈ R i ↔ s ≠ i) ∧ (∀ s k j, x s k ∈ C j ↔ k ≠ j) := by
  obtain ⟨S, hS, v, hvinj, hvVF, hcover, hvS⟩ := prism_sides hext h4 hrow
  set K := convexHull ℝ (VF : Set (E d)) with hK
  set 𝒢 := (kfaces_finite_conv VF 3).toFinset with h𝒢
  have h𝒢card : 𝒢.card = 6 := by
    rw [h𝒢, card_kfaces_eq_fvec]; exact (prism_counts hext h4 hrow).2.2.2.1
  have hmem𝒢 : ∀ G, G ∈ 𝒢 ↔ G ∈ faces K ∧ dim G = 3 := fun G => by
    rw [h𝒢, Set.Finite.mem_toFinset]; rfl
  have hS𝒢 : ∀ k, S k ∈ 𝒢 := fun k => (hmem𝒢 _).2 (hS k)
  -- the pairs
  set p : Fin 4 → E d := fun k => v ⟨2 * k, by omega⟩ with hp
  set q : Fin 4 → E d := fun k => v ⟨2 * k + 1, by omega⟩ with hq
  have hpS : ∀ k j, p k ∈ S j ↔ k ≠ j := by
    intro k j
    rw [hp]; simp only
    rw [hvS]
    constructor
    · intro h hkj; apply h; simp [hkj]
    · intro h heq; apply h; ext; simp at heq; omega
  have hqS : ∀ k j, q k ∈ S j ↔ k ≠ j := by
    intro k j
    rw [hq]; simp only
    rw [hvS]
    constructor
    · intro h hkj; apply h; simp [hkj]; omega
    · intro h heq; apply h; ext; simp at heq; omega
  have hpq : ∀ y ∈ VF, ∃ k, y = p k ∨ y = q k := by
    intro y hy
    obtain ⟨j, rfl⟩ := hcover y hy
    refine ⟨⟨j / 2, by omega⟩, ?_⟩
    rcases Nat.even_or_odd j.val with ⟨m, hm⟩ | ⟨m, hm⟩
    · left; rw [hp]; congr 1; ext; simp; omega
    · right; rw [hq]; congr 1; ext; simp; omega
  have hpVF : ∀ k, p k ∈ VF := fun k => hvVF _
  have hqVF : ∀ k, q k ∈ VF := fun k => hvVF _
  have hSinj : Function.Injective S := by
    intro k k' h
    by_contra hne
    have h1 := (hpS k k').2 hne
    rw [← h] at h1
    exact (hpS k k).1 h1 rfl
  -- the two other facets
  set 𝒮 := Finset.univ.image S with h𝒮
  have h𝒮card : 𝒮.card = 4 := by
    rw [h𝒮, Finset.card_image_of_injective _ hSinj]; rfl
  have h𝒮sub : 𝒮 ⊆ 𝒢 := by
    intro G hG
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hG
    exact hS𝒢 k
  have hTcard : (𝒢 \ 𝒮).card = 2 := by
    rw [Finset.card_sdiff_of_subset h𝒮sub, h𝒢card, h𝒮card]
  obtain ⟨T0, T1, hT01, hTeq⟩ := Finset.card_eq_two.1 hTcard
  have hT0 : T0 ∈ 𝒢 \ 𝒮 := by rw [hTeq]; simp
  have hT1 : T1 ∈ 𝒢 \ 𝒮 := by rw [hTeq]; simp
  have hTS : ∀ T ∈ 𝒢 \ 𝒮, T ∈ faces K ∧ dim T = 3 ∧ ∀ k, T ≠ S k := by
    intro T hT
    rw [Finset.mem_sdiff] at hT
    refine ⟨((hmem𝒢 T).1 hT.1).1, ((hmem𝒢 T).1 hT.1).2, fun k hk => hT.2 ?_⟩
    rw [hk, h𝒮]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  -- every vertex lies in exactly one of `T0, T1`
  have hone : ∀ y ∈ VF, ∀ k, (y = p k ∨ y = q k) → ((y ∈ T0 ∧ y ∉ T1) ∨ (y ∉ T0 ∧ y ∈ T1)) := by
    intro y hy k hyk
    have hr4 := prism_r4 hext h4 hrow y hy
    have hsplit : 𝒢.filter (fun G => y ∈ G) =
        (𝒮.filter fun G => y ∈ G) ∪ ((𝒢 \ 𝒮).filter fun G => y ∈ G) := by
      rw [← Finset.filter_union, Finset.union_sdiff_of_subset h𝒮sub]
    have hdisj : Disjoint (𝒮.filter fun G => y ∈ G) ((𝒢 \ 𝒮).filter fun G => y ∈ G) :=
      Finset.disjoint_filter_filter Finset.disjoint_sdiff
    have hside : (𝒮.filter fun G => y ∈ G).card = 3 := by
      have e : 𝒮.filter (fun G => y ∈ G) = (Finset.univ.filter fun j => j ≠ k).image S := by
        rw [h𝒮, Finset.filter_image]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hyk with rfl | rfl
        · exact (hpS k j).trans ne_comm
        · exact (hqS k j).trans ne_comm
      rw [e, Finset.card_image_of_injective _ hSinj, Finset.filter_ne',
        Finset.card_erase_of_mem (Finset.mem_univ _)]
      rfl
    rw [hsplit, Finset.card_union_of_disjoint hdisj, hside, hTeq] at hr4
    have h1 : (({T0, T1} : Finset (Set (E d))).filter fun G => y ∈ G).card = 1 := by omega
    rw [Finset.filter_insert, Finset.filter_singleton] at h1
    by_cases h0 : y ∈ T0 <;> by_cases h1' : y ∈ T1
    · simp only [h0, h1', if_true] at h1
      rw [Finset.card_insert_of_notMem (by simp [hT01])] at h1
      simp at h1
    · exact Or.inl ⟨h0, h1'⟩
    · exact Or.inr ⟨h0, h1'⟩
    · simp [h0, h1'] at h1
  -- every one of `T0, T1` meets every pair
  have hmeet : ∀ T ∈ 𝒢 \ 𝒮, ∀ k, p k ∈ T ∨ q k ∈ T := by
    intro T hT k
    by_contra hcon
    push_neg at hcon
    obtain ⟨hTf, hT3, hTne⟩ := hTS T hT
    have hsub : VF.filter (· ∈ T) ⊆ VF.filter (· ∈ S k) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      refine ⟨hy.1, ?_⟩
      obtain ⟨k', hk'⟩ := hpq y hy.1
      have hkk : k' ≠ k := by
        rintro rfl
        rcases hk' with rfl | rfl
        · exact hcon.1 hy.2
        · exact hcon.2 hy.2
      rcases hk' with rfl | rfl
      · exact (hpS k' k).2 hkk
      · exact (hqS k' k).2 hkk
    have hTsub : T ⊆ S k := by
      rw [face_eq_convexHull_filter hTf, face_eq_convexHull_filter (hS k).1]
      exact convexHull_mono (by exact_mod_cast hsub)
    have hTfS : T ∈ faces (S k) := mem_faces_of_subset (face_subset (hS k).1) hTf hTsub
    by_cases heq : T = S k
    · exact hTne k heq
    · have := dim_lt_of_mem_faces_ne hTfS heq
      rw [hT3, (hS k).2] at this
      exact lt_irrefl _ this
  -- the labelling
  have hsplitk : ∀ k, (p k ∈ T0 ∧ q k ∈ T1 ∧ p k ∉ T1 ∧ q k ∉ T0) ∨
      (q k ∈ T0 ∧ p k ∈ T1 ∧ q k ∉ T1 ∧ p k ∉ T0) := by
    intro k
    have e1 := hone (p k) (hpVF k) k (Or.inl rfl)
    have e2 := hone (q k) (hqVF k) k (Or.inr rfl)
    have m0 := hmeet T0 hT0 k
    have m1 := hmeet T1 hT1 k
    tauto
  set x : Fin 2 → Fin 4 → E d := fun s k =>
    if s = 0 then (if p k ∈ T0 then p k else q k) else (if p k ∈ T0 then q k else p k) with hx
  have hx0 : ∀ k, x 0 k ∈ T0 ∧ x 0 k ∉ T1 := by
    intro k
    simp only [hx, if_pos rfl]
    rcases hsplitk k with h | h
    · rw [if_pos h.1]; exact ⟨h.1, h.2.2.1⟩
    · rw [if_neg h.2.2.2]; exact ⟨h.1, h.2.2.1⟩
  have hx1 : ∀ k, x 1 k ∈ T1 ∧ x 1 k ∉ T0 := by
    intro k
    simp only [hx, show (1 : Fin 2) ≠ 0 by decide, if_false]
    rcases hsplitk k with h | h
    · rw [if_pos h.1]; exact ⟨h.2.1, h.2.2.2⟩
    · rw [if_neg h.2.2.2]; exact ⟨h.2.1, h.2.2.2⟩
  have hxpq : ∀ s k, x s k = p k ∨ x s k = q k := by
    intro s k
    simp only [hx]
    split_ifs <;> simp
  have hxS : ∀ s k j, x s k ∈ S j ↔ k ≠ j := by
    intro s k j
    rcases hxpq s k with h | h <;> rw [h]
    · exact hpS k j
    · exact hqS k j
  have hxR : ∀ s k i, x s k ∈ (fun i : Fin 2 => if i = 0 then T1 else T0) i ↔ s ≠ i := by
    intro s k i
    fin_cases s <;> fin_cases i <;> simp
    · exact (hx0 k).2
    · exact (hx0 k).1
    · exact (hx1 k).1
    · exact (hx1 k).2
  refine ⟨x, fun i => if i = 0 then T1 else T0, S, ?_, ?_, ?_, ?_, fun j => hS j, hxR, hxS⟩
  · -- injectivity
    intro s k s' k' h
    have hk : k = k' := by
      by_contra hne
      have h1 := (hxS s k k').2 hne
      rw [h] at h1
      exact (hxS s' k' k').1 h1 rfl
    subst hk
    refine ⟨?_, rfl⟩
    fin_cases s <;> fin_cases s'
    · rfl
    · exact absurd (h ▸ (hx0 k).1) (hx1 k).2
    · exact absurd (h ▸ (hx1 k).1) (hx0 k).2
    · rfl
  · intro s k
    rcases hxpq s k with h | h <;> rw [h]
    exacts [hpVF k, hqVF k]
  · -- every vertex is labelled
    intro y hy
    obtain ⟨k, hk⟩ := hpq y hy
    rcases hsplitk k with h | h
    · rcases hk with rfl | rfl
      · refine ⟨0, k, ?_⟩; simp only [hx, if_pos rfl, if_pos h.1]
      · refine ⟨1, k, ?_⟩; simp only [hx, show (1 : Fin 2) ≠ 0 by decide, if_false, if_pos h.1]
    · rcases hk with rfl | rfl
      · refine ⟨1, k, ?_⟩
        simp only [hx, show (1 : Fin 2) ≠ 0 by decide, if_false, if_neg h.2.2.2]
      · refine ⟨0, k, ?_⟩; simp only [hx, if_pos rfl, if_neg h.2.2.2]
  · intro i
    fin_cases i
    · exact ⟨(hTS T1 hT1).1, (hTS T1 hT1).2.1⟩
    · exact ⟨(hTS T0 hT0).1, (hTS T0 hT0).2.1⟩

end prism

end

/-! ### A prism facet of a centrally symmetric 5-polytope -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.prism_facet {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = tRow) :
    ∃ (x : Fin 2 → Fin 4 → E5) (R : Fin 2 → Set E5) (C : Fin 4 → Set E5),
      (∀ s k s' k', x s k = x s' k' → s = s' ∧ k = k') ∧
      (∀ s k, x s k ∈ P.extremePoints ℝ ∧ x s k ∈ F) ∧
      (∀ z ∈ P.extremePoints ℝ, z ∈ F → ∃ s k, z = x s k) ∧
      (∀ i, R i ∈ faces P ∧ R i ⊆ F ∧ dim (R i) = 3) ∧
      (∀ j, C j ∈ faces P ∧ C j ⊆ F ∧ dim (C j) = 3) ∧
      (∀ s k i, x s k ∈ R i ↔ s ≠ i) ∧ (∀ s k j, x s k ∈ C j ↔ k ≠ j) := by
  classical
  obtain ⟨V0, hV0⟩ := hP.polytope
  set X := (extremePoints_finite V0).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV0]
  have hPX : P = convexHull ℝ (X : Set E5) := by
    rw [hXcoe, hV0, convexHull_extremePoints_eq]
  have hFX : F ∈ faces (convexHull ℝ (X : Set E5)) := by rw [← hPX]; exact hF
  set VF := X.filter (· ∈ F) with hVF
  have hFconv : F = convexHull ℝ (VF : Set E5) := face_eq_convexHull_filter hFX
  have hext : (VF : Set E5) = (convexHull ℝ (VF : Set E5)).extremePoints ℝ := by
    rw [← hFconv, hF.2.isExtreme.extremePoints_eq, ← hXcoe]
    ext x; simp [hVF, and_comm]
  have h4' : dim (convexHull ℝ (VF : Set E5)) = 4 := by rw [← hFconv]; exact h4
  have hrow' : rowOf (convexHull ℝ (VF : Set E5)) = tRow := by
    rw [← hFconv, rowOf_face hFX, ← hPX]; exact hrow
  obtain ⟨x, R, C, hinj, hxVF, hcover, hR, hC, hxR, hxC⟩ := prism_structure hext h4' hrow'
  have hfaceP : ∀ {G : Set E5}, G ∈ faces (convexHull ℝ (VF : Set E5)) → G ∈ faces P ∧ G ⊆ F := by
    intro G hG
    refine ⟨?_, ?_⟩
    · rw [hPX]; exact faces_trans hFX (by rw [hFconv]; exact hG)
    · rw [hFconv]; exact face_subset hG
  refine ⟨x, R, C, hinj, fun s k => ?_, fun z hz hzF => ?_, fun i => ?_, fun j => ?_, hxR, hxC⟩
  · have h := Finset.mem_filter.1 (hxVF s k)
    exact ⟨by rw [← hXcoe]; exact h.1, h.2⟩
  · exact hcover z (Finset.mem_filter.2 ⟨by rw [← Finset.mem_coe, hXcoe]; exact hz, hzF⟩)
  · obtain ⟨h1, h2⟩ := hfaceP (hR i).1
    exact ⟨h1, h2, (hR i).2⟩
  · obtain ⟨h1, h2⟩ := hfaceP (hC j).1
    exact ⟨h1, h2, (hC j).2⟩

end cs

end Kalai5
