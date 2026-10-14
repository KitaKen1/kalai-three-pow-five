import Kalai5.Full.Basic
import Kalai5.Full.Rank

/-!
# Independent full normals at fourteen vertices

At `f₀ = 14` a facet with seven vertices is full; its normal (normalized to support value `1`)
takes the values `±1` at every vertex (`exists_full_normal`).  Distinct facets have distinct
normals, so nine such facets give more than eight normals, hence four linearly independent ones
(`exists_four_indep`): the hypothesis of Lemma A.
-/

namespace Kalai5

open Set Module

lemma length_filter_eq_sum {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.filter fun a => p a).length = (l.map fun a => if p a then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [List.filter_cons, h, ih] <;> ring

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **The vertices separate**: a vector orthogonal to every vertex is zero. -/
lemma IsCSPolytope5.eq_zero_of_inner_vertices {u : E5}
    (hu : ∀ x ∈ P.extremePoints ℝ, inner ℝ u x = (0 : ℝ)) : u = 0 := by
  obtain ⟨V, hV⟩ := hP.polytope
  let φ : E5 →ₗ[ℝ] ℝ := (innerSL ℝ u).toLinearMap
  have hφ : φ = 0 := by
    apply linMap_eq_zero_of_interior hP.zero_mem_interior
    intro x hx
    have hsub : P ⊆ (LinearMap.ker φ : Set E5) := by
      have hPe : P = convexHull ℝ (P.extremePoints ℝ) := by
        rw [hV]; exact (convexHull_extremePoints_eq V).symm
      rw [hPe]
      refine convexHull_min (fun a ha => ?_) (Submodule.convex _)
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      exact hu a ha
    exact hsub hx
  have := congrArg (fun f : E5 →ₗ[ℝ] ℝ => f u) hφ
  simpa [φ] using this

/-- **Four independent full normals** from nine facets with seven vertices at `f₀ = 14`. -/
theorem IsCSPolytope5.exists_indep_full_normals (h14 : fvec P 0 = 14)
    (h9 : 9 ≤ ((facetRows P).filter fun R => R.n = 7).length) :
    ∃ u : Fin 4 → E5, LinearIndependent ℝ u ∧
      ∀ i, ∀ x ∈ P.extremePoints ℝ, inner ℝ (u i) x = (1 : ℝ) ∨ inner ℝ (u i) x = (-1 : ℝ) := by
  classical
  -- the facets with seven vertices
  set FS := (hP.kfaces_finite 4).toFinset.filter fun F => cnt P F 0 = 7 with hFSdef
  have hFS : 9 ≤ FS.card := by
    rw [length_filter_eq_sum, hP.facetRows_sum (fun R => if R.n = 7 then 1 else 0)] at h9
    rw [hFSdef, Finset.card_filter]
    exact h9
  -- the normal of each
  have hnormal : ∀ F ∈ FS, ∃ v : E5, F = {x ∈ P | inner ℝ v x = (1 : ℝ)} ∧
      ∀ x ∈ P.extremePoints ℝ, inner ℝ v x = (1 : ℝ) ∨ inner ℝ v x = (-1 : ℝ) := by
    intro F hF
    simp only [hFSdef, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hF
    obtain ⟨⟨hFf, hFd⟩, hF7⟩ := hF
    have hne : F ≠ P := fun h => by have := hP.dim_self; rw [← h, hFd] at this; omega
    obtain ⟨u, -, hFu, hpm⟩ := hP.exists_full_normal hFf hne (by rw [hF7, h14])
    refine ⟨(InnerProductSpace.toDual ℝ E5).symm u, ?_, fun x hx => ?_⟩
    · rw [hFu]; simp only [InnerProductSpace.toDual_symm_apply]
    · rw [InnerProductSpace.toDual_symm_apply]; exact hpm x hx
  choose! nv hnvF hnvpm using hnormal
  have hinj : Set.InjOn nv FS := fun F hF G hG h => by rw [hnvF F hF, hnvF G hG, h]
  have hN : 8 < (FS.image nv).card := by rw [Finset.card_image_of_injOn hinj]; omega
  -- the vertex set
  obtain ⟨V, hV⟩ := hP.polytope
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  obtain ⟨u, hu, huN⟩ := exists_four_indep (N := FS.image nv) (X := X)
    (fun u hu => hP.eq_zero_of_inner_vertices fun x hx =>
      hu x (by rw [← Finset.mem_coe, hXcoe]; exact hx))
    (fun u hu x hx => by
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hu
      exact hnvpm F hF x (by rw [← hXcoe]; exact hx))
    hN
  refine ⟨u, hu, fun i x hx => ?_⟩
  obtain ⟨F, hF, hFi⟩ := Finset.mem_image.1 (huN i)
  rw [← hFi]
  exact hnvpm F hF x hx

end Kalai5
