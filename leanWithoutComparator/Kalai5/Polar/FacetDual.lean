import Kalai5.Polar.Faces
import Kalai5.Faces.LowDim

/-!
# Facets and vertices under polarity

For a polytope `K = conv V ⊆ ℝᵈ` with `0` in its interior:

* `dualFace_facet`: the dual face of a facet `G` is a single vertex `w` of `K°`, and
  `G = {x ∈ K | ⟪x, w⟫ = 1}`;
* `dualFace_vertex`: the dual face of a vertex is a facet of `K°`;
* `exists_facet_of_polar_vertex`: every vertex of `K°` is the dual of a facet of `K`;
* `exists_vertex_of_polar_facet`: every facet of `K°` is the dual of a vertex of `K`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

lemma mem_extremePoints_of_singleton_mem_faces {K : Set (E d)} {w : E d}
    (h : ({w} : Set (E d)) ∈ faces K) : w ∈ K.extremePoints ℝ :=
  isExtreme_singleton.1 h.2.isExtreme

section

variable {V : Finset (E d)} (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
include h0

lemma dim_conv_of_interior : dim (convexHull ℝ (V : Set (E d))) = d :=
  dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩

/-- The bipolar of `conv V`, written through a finite vertex set of the polar. -/
lemma exists_polar_conv :
    ∃ W : Finset (E d), polarSet (convexHull ℝ (V : Set (E d))) = convexHull ℝ (W : Set (E d)) ∧
      (0 : E d) ∈ interior (convexHull ℝ (W : Set (E d))) ∧
      polarSet (convexHull ℝ (W : Set (E d))) = convexHull ℝ (V : Set (E d)) := by
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  refine ⟨W, hW, hW ▸ zero_mem_interior_polarSet V, ?_⟩
  rw [← hW]
  exact polarSet_polarSet (convex_convexHull ℝ _) ((V.finite_toSet.isCompact_convexHull ℝ).isClosed)
    (interior_subset h0)

/-- **The dual of a facet is a vertex of the polar.** -/
lemma dualFace_facet {G : Set (E d)} (hG : G ∈ faces (convexHull ℝ (V : Set (E d))))
    (hG3 : dim G + 1 = d) :
    ∃ w, dualFace (convexHull ℝ (V : Set (E d))) G = {w} ∧
      w ∈ (polarSet (convexHull ℝ (V : Set (E d)))).extremePoints ℝ ∧
      G = {x | x ∈ convexHull ℝ (V : Set (E d)) ∧ ⟪x, w⟫ = 1} := by
  have hne : G ≠ convexHull ℝ (V : Set (E d)) := by
    intro h; have := dim_conv_of_interior h0; rw [← h] at this; omega
  have hdim := dim_dualFace h0 hG hne
  have hd0 : dim (dualFace (convexHull ℝ (V : Set (E d))) G) = 0 := by omega
  obtain ⟨w, hw⟩ := eq_singleton_of_dim_eq_zero (dualFace_nonempty h0 hG hne) hd0
  have hface := dualFace_mem_faces h0 hG hne
  rw [hw] at hface
  refine ⟨w, hw, mem_extremePoints_of_singleton_mem_faces hface, ?_⟩
  have hrec := eq_of_dualFace h0 hG hne
  rw [hw] at hrec
  rw [hrec]
  ext x
  simp

/-- **The dual of a vertex is a facet of the polar.** -/
lemma dualFace_vertex {x0 : E d} (hx0 : x0 ∈ (convexHull ℝ (V : Set (E d))).extremePoints ℝ)
    (hd : 1 ≤ d) :
    dualFace (convexHull ℝ (V : Set (E d))) {x0} ∈ faces (polarSet (convexHull ℝ (V : Set (E d)))) ∧
      dim (dualFace (convexHull ℝ (V : Set (E d))) {x0}) + 1 = d := by
  have hF : ({x0} : Set (E d)) ∈ faces (convexHull ℝ (V : Set (E d))) :=
    singleton_mem_faces_of_extreme hx0
  have hne : ({x0} : Set (E d)) ≠ convexHull ℝ (V : Set (E d)) := by
    intro h; have := dim_conv_of_interior h0; rw [← h, dim_singleton] at this; omega
  refine ⟨dualFace_mem_faces h0 hF hne, ?_⟩
  have := dim_dualFace h0 hF hne
  rw [dim_singleton] at this
  omega

/-- **Every vertex of the polar is the dual of a facet.** -/
lemma exists_facet_of_polar_vertex {w : E d}
    (hw : w ∈ (polarSet (convexHull ℝ (V : Set (E d)))).extremePoints ℝ) (hd : 1 ≤ d) :
    ∃ G ∈ faces (convexHull ℝ (V : Set (E d))), dim G + 1 = d ∧
      dualFace (convexHull ℝ (V : Set (E d))) G = {w} := by
  obtain ⟨W, hW, h0W, hbip⟩ := exists_polar_conv h0
  rw [hW] at hw
  have hF : ({w} : Set (E d)) ∈ faces (convexHull ℝ (W : Set (E d))) :=
    singleton_mem_faces_of_extreme hw
  have hne : ({w} : Set (E d)) ≠ convexHull ℝ (W : Set (E d)) := by
    intro h; have := dim_conv_of_interior h0W; rw [← h, dim_singleton] at this; omega
  set G := dualFace (convexHull ℝ (W : Set (E d))) {w} with hGdef
  have hGface := dualFace_mem_faces h0W hF hne
  rw [hbip] at hGface
  have hGdim := dim_dualFace h0W hF hne
  rw [dim_singleton] at hGdim
  refine ⟨G, hGface, by omega, ?_⟩
  obtain ⟨w', hw'eq, -, -⟩ := dualFace_facet h0 hGface (by omega)
  have hwmem : w ∈ dualFace (convexHull ℝ (V : Set (E d))) G := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hW]; exact hw.1
    · have := hx.2 w rfl
      rwa [real_inner_comm] at this
  rw [hw'eq] at hwmem ⊢
  rw [Set.mem_singleton_iff] at hwmem
  rw [hwmem]

/-- **Every facet of the polar is the dual of a vertex.** -/
lemma exists_vertex_of_polar_facet {Φ : Set (E d)}
    (hΦ : Φ ∈ faces (polarSet (convexHull ℝ (V : Set (E d))))) (hΦ3 : dim Φ + 1 = d) :
    ∃ x0 ∈ (convexHull ℝ (V : Set (E d))).extremePoints ℝ,
      Φ = dualFace (convexHull ℝ (V : Set (E d))) {x0} := by
  obtain ⟨W, hW, h0W, hbip⟩ := exists_polar_conv h0
  rw [hW] at hΦ
  have hne : Φ ≠ convexHull ℝ (W : Set (E d)) := by
    intro h; have := dim_conv_of_interior h0W; rw [← h] at this; omega
  have hdim := dim_dualFace h0W hΦ hne
  obtain ⟨x0, hx0⟩ := eq_singleton_of_dim_eq_zero (dualFace_nonempty h0W hΦ hne) (by omega)
  have hface := dualFace_mem_faces h0W hΦ hne
  rw [hx0, hbip] at hface
  refine ⟨x0, mem_extremePoints_of_singleton_mem_faces hface, ?_⟩
  have hrec := eq_of_dualFace h0W hΦ hne
  rw [hx0] at hrec
  rw [hrec]
  ext y
  simp only [dualFace, Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, hW]
  rw [real_inner_comm]

/-- Incidence of a vertex and a facet through the dual vertex of the facet. -/
lemma mem_facet_iff_dual {G : Set (E d)} (hG : G ∈ faces (convexHull ℝ (V : Set (E d))))
    (hG3 : dim G + 1 = d) {w : E d} (hw : dualFace (convexHull ℝ (V : Set (E d))) G = {w})
    {x : E d} (hx : x ∈ convexHull ℝ (V : Set (E d))) :
    x ∈ G ↔ ⟪x, w⟫ = 1 := by
  obtain ⟨w', hw', -, hGeq⟩ := dualFace_facet h0 hG hG3
  rw [hw] at hw'
  have : w = w' := Set.singleton_eq_singleton_iff.1 hw'
  subst this
  conv_lhs => rw [hGeq]
  simp [hx]

end

end Kalai5
