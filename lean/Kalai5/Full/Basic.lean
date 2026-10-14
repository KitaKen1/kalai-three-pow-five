import Kalai5.Faces.Counting
import Kalai5.Faces.LowDim

/-!
# Full facets

A proper face `F` of a centrally symmetric 5-polytope with half of the vertices (`2 #V(F) = f₀`)
is **full**: it contains one vertex of every antipodal pair.  Then

* every vertex lies in `F` or in `-F` (`vertex_mem_or_neg_mem_of_full`);
* after normalising its exposing functional, `u ≤ 1` on `P`, `F = P ∩ {u = 1}` and `u = ±1` at
  every vertex (`exists_full_normal`): all vertices lie on the two parallel hyperplanes
  `u = ±1`, i.e. `P` is the Cayley polytope of `F` and `-F`;
* `P = conv (F ∪ -F)` (`eq_convexHull_full`).
-/

namespace Kalai5

open Set

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **In a full face, every vertex or its antipode lies in the face.** -/
lemma IsCSPolytope5.vertex_mem_or_neg_mem_of_full {F : Set E5} (hF : F ∈ faces P) (hne : F ≠ P)
    (hfull : 2 * cnt P F 0 = fvec P 0) {v : Set E5} (hv : v ∈ faces P) (hv0 : dim v = 0) :
    v ⊆ F ∨ -v ⊆ F := by
  set A := {G | G ∈ faces P ∧ G ⊆ F ∧ dim G = 0} with hAdef
  have hAfin : A.Finite := hP.below_finite F 0
  have hVfin : {G | G ∈ faces P ∧ dim G = 0}.Finite := hP.kfaces_finite 0
  have himg : ((fun G : Set E5 => -G) '' A).ncard = A.ncard :=
    Set.ncard_image_of_injective _ neg_injective
  have hdisj : Disjoint A ((fun G : Set E5 => -G) '' A) := by
    rw [Set.disjoint_left]
    rintro G ⟨-, hGF, -⟩ ⟨G', ⟨hG', hG'F, -⟩, rfl⟩
    obtain ⟨x, hx⟩ := hG'.1
    have h1 : x ∈ F := hG'F hx
    have h2 : -x ∈ F := hGF (by simpa using hx)
    exact hne (hP.eq_of_mem_of_neg_mem hF h1 h2)
  have hsub : A ∪ ((fun G : Set E5 => -G) '' A) ⊆ {G | G ∈ faces P ∧ dim G = 0} := by
    rintro G (⟨hG, -, hd⟩ | ⟨G', ⟨hG', -, hd'⟩, rfl⟩)
    · exact ⟨hG, hd⟩
    · exact ⟨neg_mem_faces hP.symm hG', by rw [dim_neg]; exact hd'⟩
  have hcard : (A ∪ ((fun G : Set E5 => -G) '' A)).ncard = {G | G ∈ faces P ∧ dim G = 0}.ncard := by
    rw [Set.ncard_union_eq hdisj hAfin (hAfin.image _), himg]
    show A.ncard + A.ncard = fvec P 0
    rw [← hfull]; show A.ncard + A.ncard = 2 * A.ncard; ring
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard.ge hVfin
  have hmem : v ∈ A ∪ ((fun G : Set E5 => -G) '' A) := by rw [heq]; exact ⟨hv, hv0⟩
  rcases hmem with ⟨-, hvF, -⟩ | ⟨G', ⟨-, hG'F, -⟩, rfl⟩
  · exact Or.inl hvF
  · right; simpa using hG'F

/-- **Normal of a full facet**: `u ≤ 1` on `P`, `F = P ∩ {u = 1}`, and `u = ±1` at every
vertex. -/
lemma IsCSPolytope5.exists_full_normal {F : Set E5} (hF : F ∈ faces P) (hne : F ≠ P)
    (hfull : 2 * cnt P F 0 = fvec P 0) :
    ∃ u : StrongDual ℝ E5, (∀ x ∈ P, u x ≤ 1) ∧ F = {x ∈ P | u x = 1} ∧
      ∀ x ∈ P.extremePoints ℝ, u x = 1 ∨ u x = -1 := by
  obtain ⟨l, hl⟩ := exists_functional hF
  obtain ⟨x0, hx0⟩ := hF.1
  have hx0' := hx0
  rw [hl] at hx0'
  set M := l x0
  have h0P : (0 : E5) ∈ P := interior_subset hP.zero_mem_interior
  have hM0 : 0 ≤ M := by have := hx0'.2 0 h0P; simpa using this
  have hMpos : 0 < M := by
    rcases lt_or_eq_of_le hM0 with h | h
    · exact h
    · exfalso
      have h0F : (0 : E5) ∈ F := by
        rw [hl]; exact ⟨h0P, fun y hy => by rw [map_zero, h]; exact hx0'.2 y hy⟩
      exact hne (face_eq_of_mem_interior hF h0F hP.zero_mem_interior)
  refine ⟨M⁻¹ • l, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · have := hx0'.2 x hx
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_le_one₀ hMpos]; exact this
  · ext x
    simp only [Set.mem_setOf_eq, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    constructor
    · intro hxF
      have hxF' := hxF; rw [hl] at hxF'
      refine ⟨hxF'.1, ?_⟩
      have h1 := hxF'.2 x0 hx0'.1
      have h2 := hx0'.2 x hxF'.1
      rw [inv_mul_eq_one₀ hMpos.ne']; linarith
    · rintro ⟨hxP, hx1⟩
      rw [inv_mul_eq_one₀ hMpos.ne'] at hx1
      rw [hl]; exact ⟨hxP, fun y hy => by rw [← hx1]; exact hx0'.2 y hy⟩
  · obtain ⟨V, hV⟩ := hP.polytope
    have hxv : ({x} : Set E5) ∈ faces P := by
      rw [hV]; exact singleton_mem_faces_of_extreme (by rw [← hV]; exact hx)
    rcases hP.vertex_mem_or_neg_mem_of_full hF hne hfull hxv (dim_singleton x) with h | h
    · left
      have hxF : x ∈ F := h rfl
      rw [hl] at hxF
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      rw [inv_mul_eq_one₀ hMpos.ne']
      exact le_antisymm (hxF.2 x0 hx0'.1) (hx0'.2 x hxF.1)
    · right
      have hxF : -x ∈ F := h (by simp)
      rw [hl] at hxF
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      have : l (-x) = M := le_antisymm (hx0'.2 (-x) hxF.1) (hxF.2 x0 hx0'.1)
      rw [map_neg] at this
      rw [show l x = -M by linarith, mul_neg, inv_mul_cancel₀ hMpos.ne']

/-- **A full facet and its antipode span `P`.** -/
lemma IsCSPolytope5.eq_convexHull_full {F : Set E5} (hF : F ∈ faces P) (hne : F ≠ P)
    (hfull : 2 * cnt P F 0 = fvec P 0) : P = convexHull ℝ (F ∪ -F) := by
  obtain ⟨V, hV⟩ := hP.polytope
  apply le_antisymm
  · have hext : P.extremePoints ℝ ⊆ F ∪ -F := by
      intro x hx
      have hxv : ({x} : Set E5) ∈ faces P := by
        rw [hV]; exact singleton_mem_faces_of_extreme (by rw [← hV]; exact hx)
      rcases hP.vertex_mem_or_neg_mem_of_full hF hne hfull hxv (dim_singleton x) with h | h
      · exact Or.inl (h rfl)
      · right; have := h (by simp : -x ∈ -({x} : Set E5)); simpa using this
    calc P = convexHull ℝ (P.extremePoints ℝ) := by
          rw [hV]; exact (convexHull_extremePoints_eq V).symm
      _ ⊆ convexHull ℝ (F ∪ -F) := convexHull_mono hext
  · apply convexHull_min _ hP.convex
    rintro x (hx | hx)
    · exact face_subset hF hx
    · have := face_subset hF (show -x ∈ F from hx)
      simpa using hP.symm _ this

end Kalai5
