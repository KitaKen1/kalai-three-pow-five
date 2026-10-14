import Kalai5.FullPrism.Interface
import Kalai5.FullPrism.Structure

/-!
# The full tetrahedron prism lemma

`IsCSPolytope5.full_prism`: a centrally symmetric 5-polytope with sixteen vertices and a facet
with row `(8,16,14,6; 32)` (combinatorially `Δ₃ × I`) has at least 243 nonempty faces.

The facet `F` is full.  `prism_sides` labels its vertices `v⁺_k, v⁻_k` by the side facets `S_k`
they miss; for each side, `r_k = M_k u - l_k` (with `l_k` exposing `S_k` in `P` at level `M_k`)
vanishes on `S_k` and is positive at `v^±_k`.  Then `three_pow_five_of_prism_labels`.
(No bound on `f₄` is needed.)
-/

namespace Kalai5

open Set FullPrism

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {P : Set E5}

theorem IsCSPolytope5.full_prism (hP : IsCSPolytope5 P) (h16 : fvec P 0 = 16)
    (hT : tRow ∈ facetRows P) : 243 ≤ (faces P).ncard := by
  classical
  obtain ⟨F, hF, hF4, hrowF⟩ := hP.mem_facetRows hT
  have hne : F ≠ P := fun h => by have := hP.dim_self; rw [← h, hF4] at this; omega
  have hcnt : cnt P F 0 = 8 := congrArg Row.n hrowF
  have hfull : 2 * cnt P F 0 = fvec P 0 := by rw [hcnt, h16]
  -- the vertex set of `P`
  obtain ⟨V0, hV0⟩ := hP.polytope
  set X := (extremePoints_finite V0).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV0]
  have hPX : P = convexHull ℝ (X : Set E5) := by
    rw [hXcoe, hV0, convexHull_extremePoints_eq]
  have hFX : F ∈ faces (convexHull ℝ (X : Set E5)) := by rw [← hPX]; exact hF
  -- the facet as a polytope
  set VF := X.filter (· ∈ F) with hVF
  have hFconv : F = convexHull ℝ (VF : Set E5) := face_eq_convexHull_filter hFX
  have hext : (VF : Set E5) = (convexHull ℝ (VF : Set E5)).extremePoints ℝ := by
    rw [← hFconv, hF.2.isExtreme.extremePoints_eq, ← hXcoe]
    ext x; simp [hVF, and_comm]
  have h4 : dim (convexHull ℝ (VF : Set E5)) = 4 := by rw [← hFconv]; exact hF4
  have hrow : rowOf (convexHull ℝ (VF : Set E5)) = tRow := by
    rw [← hFconv, rowOf_face hFX, ← hPX]; exact hrowF
  obtain ⟨S, hS, v, hvinj, hvVF, hcover, hvS⟩ := prism_sides hext h4 hrow
  -- the full normal
  obtain ⟨u, hu1, hFu, -⟩ := hP.exists_full_normal hF hne hfull
  -- the side forms
  have hSP : ∀ k, S k ∈ faces P := by
    intro k
    rw [hPX]
    exact faces_trans hFX (by rw [hFconv]; exact (hS k).1)
  have hform : ∀ k, ∃ r : E5, (∀ x ∈ F, x ∈ S k → ⟪r, x⟫ = 0) ∧
      (∀ x ∈ F, x ∉ S k → 0 < ⟪r, x⟫) := by
    intro k
    obtain ⟨l, hl⟩ := exists_functional (hSP k)
    obtain ⟨x0, hx0⟩ := (hSP k).1
    have hx0' := hx0
    rw [hl] at hx0'
    set M := l x0
    refine ⟨(InnerProductSpace.toDual ℝ E5).symm (M • u - l), fun x hxF hxS => ?_,
      fun x hxF hxS => ?_⟩
    · rw [InnerProductSpace.toDual_symm_apply]
      have hux : u x = 1 := by rw [hFu] at hxF; exact hxF.2
      have hxS' := hxS
      rw [hl] at hxS'
      have h1 := hxS'.2 x0 hx0'.1
      have h2 := hx0'.2 x hxS'.1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        smul_eq_mul, hux, mul_one]
      linarith
    · rw [InnerProductSpace.toDual_symm_apply]
      have hux : u x = 1 := by rw [hFu] at hxF; exact hxF.2
      have hxP : x ∈ P := face_subset hF hxF
      have hlt : l x < M := by
        by_contra hge
        push_neg at hge
        apply hxS
        rw [hl]
        exact ⟨hxP, fun y hy => le_trans (hx0'.2 y hy) hge⟩
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        smul_eq_mul, hux, mul_one]
      linarith
  choose r hr0' hrpos using hform
  have hvF : ∀ j, v j ∈ F := fun j => (Finset.mem_filter.1 (hvVF j)).2
  have hvext : ∀ j, v j ∈ P.extremePoints ℝ := fun j => by
    rw [← hXcoe]; exact (Finset.mem_filter.1 (hvVF j)).1
  refine hP.three_pow_five_of_prism_labels hF hne hfull v hvF hvext hvinj ?_ r ?_ ?_ ?_
  · intro x hx hxF
    exact hcover x (Finset.mem_filter.2 ⟨by rw [← Finset.mem_coe, hXcoe]; exact hx, hxF⟩)
  · intro k j hj
    exact hr0' k (v j) (hvF j) ((hvS k j).2 hj)
  · intro k
    apply hrpos k _ (hvF _)
    rw [hvS]
    simp only [not_not]
    omega
  · intro k
    apply hrpos k _ (hvF _)
    rw [hvS]
    simp only [not_not]
    omega

end Kalai5
