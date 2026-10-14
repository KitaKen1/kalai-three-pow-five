import Kalai5.Rigidity.Slice

/-!
# Consequences of the slice correspondence

For a vertex `a₀` of `R = conv V`:

* `extremePoints_Q`: the vertices of the slice are the points `e y` on edges `[a₀, y]`;
* `vectorSpan_le_edges` (vertex cone): the edges at `a₀` span the directions of `R`;
* `exists_edge`: a vertex of a polytope of dimension `≥ 1` lies on an edge;
* `vectorSpan_le_twoFaces` (at an edge): the vertices of the `2`-faces containing an edge
  `[a₀, q]` span the directions of `R` (dimension `≥ 2`).
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-- Points of a convex hull lie in the span of the differences to any base point. -/
lemma sub_mem_span_of_mem_convexHull {S : Set (E n)} {p a : E n} (hp : p ∈ convexHull ℝ S)
    (hS : S.Nonempty) : p - a ∈ Submodule.span ℝ ((fun s => s - a) '' S) := by
  obtain ⟨s₀, hs₀⟩ := hS
  have hp' : p ∈ affineSpan ℝ S := convexHull_subset_affineSpan S hp
  have h1 : p -ᵥ s₀ ∈ vectorSpan ℝ S := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hp' (subset_affineSpan ℝ S hs₀)
  have hle : vectorSpan ℝ S ≤ Submodule.span ℝ ((fun s => s - a) '' S) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    dsimp only
    have : x -ᵥ y = (x - a) - (y - a) := by rw [vsub_eq_sub]; abel
    rw [SetLike.mem_coe, this]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨x, hx, rfl⟩)
      (Submodule.subset_span ⟨y, hy, rfl⟩)
  have e : p - a = (p -ᵥ s₀) + (s₀ - a) := by rw [vsub_eq_sub]; abel
  rw [e]
  exact Submodule.add_mem _ (hle h1) (Submodule.subset_span ⟨s₀, hs₀, rfl⟩)

namespace VSlice

variable {V : Finset (E n)} {a₀ : E n} (σ : VSlice V a₀)

/-- The slice points. -/
noncomputable def W : Finset (E n) := (V.erase a₀).image σ.e

lemma coe_W : (σ.W : Set (E n)) = σ.e '' ((V : Set (E n)) \ {a₀}) := by
  simp [W, Finset.coe_image, Finset.coe_erase]

lemma Q_eq' : σ.Q = convexHull ℝ (σ.W : Set (E n)) := by rw [coe_W, Q_eq]

/-- **The vertices of the slice lie on edges at `a₀`.** -/
theorem extremePoints_Q {z : E n} (hz : z ∈ σ.Q.extremePoints ℝ) :
    ∃ y ∈ V, y ≠ a₀ ∧ z = σ.e y ∧
      ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧ a₀ ∈ F ∧ y ∈ F := by
  rw [Q_eq'] at hz
  have hzW := extremePoints_convexHull_subset hz
  rw [coe_W] at hzW
  obtain ⟨y, ⟨hyV, hya⟩, rfl⟩ := hzW
  have hya' : y ≠ a₀ := by simpa using hya
  refine ⟨y, hyV, hya', rfl, ?_⟩
  have hface := singleton_mem_faces_of_extreme hz
  rw [← Q_eq'] at hface
  obtain ⟨F, hF, haF, hne, hFH⟩ := σ.exists_face_of_mem_faces hface
  have hdim := σ.dim_inter_add_one hF haF hne
  rw [hFH, dim_singleton] at hdim
  have heF : σ.e y ∈ F := (hFH.symm ▸ rfl : σ.e y ∈ F ∩ σ.H).1
  exact ⟨F, hF, by omega, haF, (σ.e_mem_iff hF haF hyV hya').1 heF⟩

end VSlice

/-- A nonempty polytope has an extreme point. -/
lemma exists_extremePoint {S : Finset (E n)} (hS : S.Nonempty) :
    ((convexHull ℝ (S : Set (E n))).extremePoints ℝ).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have := convexHull_extremePoints_eq S
  rw [h, convexHull_empty] at this
  obtain ⟨s, hs⟩ := hS
  have hs' : s ∈ convexHull ℝ (S : Set (E n)) := subset_convexHull ℝ _ hs
  rw [← this] at hs'
  exact hs'

/-- **Vertex cone**: the edges at a vertex span the directions of the polytope. -/
theorem vectorSpan_le_edges {V : Finset (E n)} {a₀ : E n}
    (ha : a₀ ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ) :
    vectorSpan ℝ (V : Set (E n)) ≤ Submodule.span ℝ ((fun y => y - a₀) ''
      {y | y ∈ V ∧ ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧ a₀ ∈ F ∧ y ∈ F}) := by
  classical
  obtain ⟨σ⟩ := exists_vslice ha
  have ha₀ : a₀ ∈ V := σ.ha₀
  rw [vectorSpan_eq_span_vsub_set_right ℝ (show a₀ ∈ (V : Set (E n)) by exact_mod_cast ha₀),
    Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  by_cases hxa : x = a₀
  · rw [hxa, vsub_self]; exact Submodule.zero_mem _
  set N := {y | y ∈ V ∧ ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧ a₀ ∈ F ∧ y ∈ F}
  -- the slice point `e x` lies in the hull of the slice vertices
  have hxQ : σ.e x ∈ σ.Q := by
    rw [σ.Q_eq']
    exact subset_convexHull ℝ _ (by rw [σ.coe_W]; exact ⟨x, ⟨hx, by simpa using hxa⟩, rfl⟩)
  have hWne : σ.W.Nonempty := ⟨σ.e x, by
    simp only [VSlice.W, Finset.mem_image]; exact ⟨x, Finset.mem_erase.2 ⟨hxa, hx⟩, rfl⟩⟩
  have hext := convexHull_extremePoints_eq σ.W
  rw [← σ.Q_eq'] at hext
  rw [← hext] at hxQ
  have hEne := exists_extremePoint hWne
  rw [← σ.Q_eq'] at hEne
  have h1 := sub_mem_span_of_mem_convexHull (a := a₀) hxQ hEne
  -- each slice vertex `e y` comes from an edge `[a₀, y]`
  have h2 : Submodule.span ℝ ((fun s => s - a₀) '' σ.Q.extremePoints ℝ) ≤
      Submodule.span ℝ ((fun y => y - a₀) '' N) := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hyV, hya, rfl, F, hF, hF1, haF, hyF⟩ := σ.extremePoints_Q hz
    dsimp only
    rw [σ.e_sub]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, ⟨hyV, F, hF, hF1, haF, hyF⟩, rfl⟩)
  have h3 := h2 h1
  rw [σ.e_sub] at h3
  have hτ := σ.τ_pos hx hxa
  have : x -ᵥ a₀ = (σ.τ x)⁻¹ • (σ.τ x • (x - a₀)) := by
    rw [smul_smul, inv_mul_cancel₀ hτ.ne', one_smul, vsub_eq_sub]
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ h3

/-- **A vertex of a polytope of positive dimension lies on an edge.** -/
theorem exists_edge {V : Finset (E n)} {a₀ : E n}
    (ha : a₀ ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ)
    (hdim : 1 ≤ dim (convexHull ℝ (V : Set (E n)))) :
    ∃ y ∈ V, y ≠ a₀ ∧ ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧ a₀ ∈ F ∧ y ∈ F := by
  by_contra hcon
  push_neg at hcon
  have h := vectorSpan_le_edges ha
  have hbot : Submodule.span ℝ ((fun y => y - a₀) ''
      {y | y ∈ V ∧ ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧ a₀ ∈ F ∧ y ∈ F}) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, ⟨hyV, F, hF, hF1, haF, hyF⟩, rfl⟩
    dsimp only
    by_cases hya : y = a₀
    · rw [hya, sub_self]
    · exact absurd hyF (hcon y hyV hya F hF hF1 haF)
  rw [hbot] at h
  have h0 : dim (V : Set (E n)) = 0 := by
    unfold dim; rw [le_bot_iff.1 h, finrank_bot]
  rw [dim_convexHull', h0] at hdim
  omega

namespace VSlice

variable {V : Finset (E n)} {a₀ : E n} (σ : VSlice V a₀)

/-- An edge `[a₀, q]` cuts the vertex `e q` of the slice. -/
lemma e_extreme_of_edge {F : Set (E n)} (hF : F ∈ faces (convexHull ℝ (V : Set (E n))))
    (hF1 : dim F = 1) (haF : a₀ ∈ F) {q : E n} (hqV : q ∈ V) (hqa : q ≠ a₀) (hqF : q ∈ F) :
    σ.e q ∈ σ.Q.extremePoints ℝ := by
  have hne : F ≠ {a₀} := by
    intro h; rw [h, dim_singleton] at hF1; omega
  have hface := σ.inter_mem_faces hF haF hne
  have hdim := σ.dim_inter_add_one hF haF hne
  rw [hF1] at hdim
  -- a `0`-dimensional face is a singleton
  obtain ⟨g, hg⟩ := eq_singleton_of_dim_eq_zero hface.1 (by omega)
  have heq : σ.e q ∈ F ∩ σ.H := ⟨(σ.e_mem_iff hF haF hqV hqa).2 hqF, σ.e_mem_H hqV hqa⟩
  rw [hg] at heq hface
  rw [Set.mem_singleton_iff.1 heq]
  exact isExtreme_singleton.1 hface.2.isExtreme

end VSlice

/-- **At an edge `[a₀, q]`, the `2`-faces containing it span** (dimension `≥ 2`). -/
theorem vectorSpan_le_twoFaces {V : Finset (E n)} {a₀ q : E n}
    (ha : a₀ ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ) (hqV : q ∈ V) (hqa : q ≠ a₀)
    {F : Set (E n)} (hF : F ∈ faces (convexHull ℝ (V : Set (E n)))) (hF1 : dim F = 1)
    (haF : a₀ ∈ F) (hqF : q ∈ F) (hdim : 2 ≤ dim (convexHull ℝ (V : Set (E n)))) :
    vectorSpan ℝ (V : Set (E n)) ≤ Submodule.span ℝ ((fun z => z - a₀) ''
      {z | z ∈ V ∧ ∃ G ∈ faces (convexHull ℝ (V : Set (E n))), dim G = 2 ∧ a₀ ∈ G ∧ q ∈ G ∧
        z ∈ G}) := by
  classical
  obtain ⟨σ⟩ := exists_vslice ha
  have ha₀ : a₀ ∈ V := σ.ha₀
  set X := {z | z ∈ V ∧ ∃ G ∈ faces (convexHull ℝ (V : Set (E n))), dim G = 2 ∧ a₀ ∈ G ∧ q ∈ G ∧
    z ∈ G}
  -- the vertex `e q` of the slice and the edges at it
  have heq := σ.e_extreme_of_edge hF hF1 haF hqV hqa hqF
  rw [σ.Q_eq'] at heq
  have hcone := vectorSpan_le_edges heq
  have hspanX : ∀ y ∈ V, y ≠ a₀ → σ.e y ∈ σ.W →
      (∃ Φ ∈ faces (convexHull ℝ (σ.W : Set (E n))), dim Φ = 1 ∧ σ.e q ∈ Φ ∧ σ.e y ∈ Φ) →
      y ∈ X ∧ q ∈ X := by
    rintro y hyV hya - ⟨Φ, hΦ, hΦ1, hqΦ, hyΦ⟩
    rw [← σ.Q_eq'] at hΦ
    obtain ⟨G, hG, haG, hGne, hGH⟩ := σ.exists_face_of_mem_faces hΦ
    have hdimG := σ.dim_inter_add_one hG haG hGne
    rw [hGH, hΦ1] at hdimG
    have hqG : q ∈ G := (σ.e_mem_iff hG haG hqV hqa).1 (hGH ▸ hqΦ).1
    have hyG : y ∈ G := (σ.e_mem_iff hG haG hyV hya).1 (hGH ▸ hyΦ).1
    exact ⟨⟨hyV, G, hG, by omega, haG, hqG, hyG⟩, ⟨hqV, G, hG, by omega, haG, hqG, hqG⟩⟩
  -- the slice has dimension `≥ 1`, so `e q` has an edge, hence `q ∈ X`
  have hdimQ := σ.dim_Q_add_one (by omega)
  have hdimW : 1 ≤ dim (convexHull ℝ (σ.W : Set (E n))) := by rw [← σ.Q_eq']; omega
  obtain ⟨w, hwW, hwq, Φ, hΦ, hΦ1, hqΦ, hwΦ⟩ := exists_edge heq hdimW
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ V.erase a₀, σ.e y = w := by
    simpa [VSlice.W] using hwW
  have hqX : q ∈ X :=
    (hspanX y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy) hwW ⟨Φ, hΦ, hΦ1, hqΦ, hwΦ⟩).2
  -- every direction of `R` is in the span
  rw [vectorSpan_eq_span_vsub_set_right ℝ (show a₀ ∈ (V : Set (E n)) by exact_mod_cast ha₀),
    Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  by_cases hxa : x = a₀
  · rw [hxa, vsub_self]; exact Submodule.zero_mem _
  have hxW : σ.e x ∈ σ.W := by
    simp only [VSlice.W, Finset.mem_image]; exact ⟨x, Finset.mem_erase.2 ⟨hxa, hx⟩, rfl⟩
  have h1 : σ.e x - σ.e q ∈ Submodule.span ℝ ((fun w => w - σ.e q) ''
      {w | w ∈ σ.W ∧ ∃ Φ ∈ faces (convexHull ℝ (σ.W : Set (E n))), dim Φ = 1 ∧ σ.e q ∈ Φ ∧
        w ∈ Φ}) := by
    have := hcone (vsub_mem_vectorSpan ℝ (show σ.e x ∈ (σ.W : Set (E n)) by exact_mod_cast hxW)
      (show σ.e q ∈ (σ.W : Set (E n)) by
        simp only [Finset.mem_coe, VSlice.W, Finset.mem_image]
        exact ⟨q, Finset.mem_erase.2 ⟨hqa, hqV⟩, rfl⟩))
    rwa [vsub_eq_sub] at this
  have hsub : Submodule.span ℝ ((fun w => w - σ.e q) ''
      {w | w ∈ σ.W ∧ ∃ Φ ∈ faces (convexHull ℝ (σ.W : Set (E n))), dim Φ = 1 ∧ σ.e q ∈ Φ ∧
        w ∈ Φ}) ≤ Submodule.span ℝ ((fun z => z - a₀) '' X) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, ⟨hwW, Φ, hΦ, hΦ1, hqΦ, hwΦ⟩, rfl⟩
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ V.erase a₀, σ.e y = w := by
      simpa [VSlice.W] using hwW
    have hyX := (hspanX y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy) hwW
      ⟨Φ, hΦ, hΦ1, hqΦ, hwΦ⟩).1
    dsimp only
    have e : σ.e y - σ.e q = σ.τ y • (y - a₀) - σ.τ q • (q - a₀) := by
      rw [← σ.e_sub, ← σ.e_sub]; abel
    rw [SetLike.mem_coe, e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hyX, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hqX, rfl⟩))
  have h2 := hsub h1
  have hτ := σ.τ_pos hx hxa
  have e : x -ᵥ a₀ = (σ.τ x)⁻¹ • ((σ.e x - σ.e q) + σ.τ q • (q - a₀)) := by
    rw [show (σ.e x - σ.e q) + σ.τ q • (q - a₀) = σ.e x - a₀ by rw [← σ.e_sub]; abel, σ.e_sub,
      smul_smul, inv_mul_cancel₀ hτ.ne', one_smul, vsub_eq_sub]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ h2
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hqX, rfl⟩)))

end Kalai5
